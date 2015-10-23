module Ling.Reduce where

import           Control.Lens
import           Data.Maybe   (fromMaybe)

import           Ling.Norm
import           Ling.Scoped
import           Ling.Session
import           Ling.Utils hiding (subst1)

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
