{-# LANGUAGE Rank2Types #-}
module Ling.Reduce where

import           Ling.Norm
import           Ling.Scoped
import           Ling.Session
import           Ling.Prelude hiding (subst1)

app :: Name -> Scoped Term -> [Term] -> Scoped Term
app _ st []     = reduceWHNF st
app d st (u:us) =
  let st' = reduceWHNF st in
  case st'^.scoped of
    Lam (Arg x _) t' -> app d (subst1 d (x,u) (st' & scoped .~ t')) us
    Def x es         -> st' & scoped .~ Def x (es ++ u:us)
    _                -> error "Ling.Subst.app: IMPOSSIBLE"

reduceCase :: Scoped Term -> [Branch] -> Scoped Term
reduceCase st brs = case st'^.scoped of
  Con{} -> reduceWHNF scase
  _     -> scase
  where st'   = reduceWHNF st
        scase = (`mkCase` brs) <$> st'

reduceWHNF :: Scoped Term -> Scoped Term
reduceWHNF st =
  case st^.scoped of
    Case e brs -> reduceCase (st & scoped .~ e) brs
    TSession (TermS p t') -> dualOp p $ reduceWHNF (st & scoped .~ t')
    Def d es -> fromMaybe st (app d <$> unDef (st & scoped .~ d) <*> pure es)
    _ -> st

reduceWHNFWith :: Traversal' s Term -> Scoped s -> Scoped s
reduceWHNFWith trv (Scoped defs s) = trv (reduceWHNF . Scoped defs) s

flatRSession :: Scoped RSession -> [Scoped RSession]
flatRSession ssr@(Scoped defs (Repl s r)) =
  case () of
  _ | Just n <- isLitR r'       -> replicate (fromInteger n) (pure $ oneS s)
  _ | Just (r0,r1) <- isAddR r' -> flatRSession (Scoped defs' $ s `Repl` r0)
                                ++ flatRSession (Scoped defs' $ s `Repl` r1)
  _                             -> [ssr]
  where Scoped defs' r' = reduceWHNFWith rterm (Scoped defs r)

flatSessions :: Scoped Sessions -> Scoped Sessions
flatSessions (Scoped defs ss) =
  sequenceA $ ss >>= flatRSession . Scoped defs
