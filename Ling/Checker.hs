{-
channelCD :: Lens' Channel ChanDec
channelCD (ChanDec c s) = fmap (\c' -> ChanDec c s)
-}
{-
atMostOne :: (a -> Bool) -> [a] -> Bool
atMostOne p xs = case filter p xs of
  []  -> True
  [_] -> True
  _   -> False
-}

{-
data ConstraintStatus = AlreadySolved | Outside | ReadyForSplit -- | Unsolvable
  deriving (Eq)

constraintStatus :: Constraint -> Proto -> ConstraintStatus
constraintStatus cs p
  -- | size cs == 0 = error "nullary constraint"
  -- | size cs == 1 = error "unary constraint"
  | cs `elem` p ^. constraints = AlreadySolved
  | otherwise =
    case filter (chanPresent p) (s2l cs) of
      []  -> Outside
      [_] -> ReadyForSplit
      _   -> error "Unsolvable"
-}

{-
solvedConstraint :: Constraint -> Proto -> Bool
solvedConstraint cs p =
  (cs `elem` p ^. constraints) &&
    case filter (chanPresent p) (s2l cs) of
      []  -> True
      [_] -> True
      cs' -> False

checkConstraint :: Constraint -> Proto -> TC ()
checkConstraint cs p =
  when (not (solvedConstraint cs p)) $
    throwError "checkConstraint!"
-}

{-
cleanConstraints :: Constraints -> Constraints
cleanConstraints = Set.filter ((> 1) . size)
-}

{-
debugConstraints :: TC a -> TC a
debugConstraints m = do
  ks <- asks _chanConstraints -- LENS-ME
  if ks ^. noConstraints
    then debug ["No constraints."]
    else debug $ "Current constraints independant channels:"
               : map ("  " ++) (prettyConstraints ks)
  m
-}
{-
substChans :: Proto -> ([Channel], (Channel, NSession)) -> Proto
substChans proto (ds, (c,s)) =
  proto & chans %~ rmKeys ds
        & chans . at c .~ Just s
        & constraints %~ mapConstraints (Constraint.subst (l2s ds, l2s [c]))
-}
{-
reduceHead :: NTerm -> TC NTerm
reduceHead e = case e of
  NDef x es ->
    do me <- asks (\z -> z ^. edefs . at x)
       case (me, es) of
         (Nothing, _)  -> return e
         (Just e', []) -> return e'
         (Just e', _)  -> throwError $ "reducedHead/NDef " ++ pretty e' ++ " " ++ pretty es
  NAnn s _  -> reduceHead s

  NFun{}    -> return e
  NSig{}    -> return e
  NTyp      -> return e
  NLit{}    -> return e
  NProc{}   -> return e
  NProto{}  -> return e
-}

{-
class Conv a where
  (===) :: a -> a -> TC Bool

instance Conv NTerm where
  t0 === t1 = t0 == t1 ||> t0 ==== t1 -- join (liftA2 (====) (reduceHead t0) (reduceHead t1))
   where
    NFun x0 es0 ==== NFun x1 es1 = x0 === x1 <&&> es0 === es1
    NSig x0 es0 ==== NSig x1 es1 = x0 === x1 <&&> es0 === es1
    NDef x0 es0 ==== NDef x1 es1 = x0 == x1 &&> es0 === es1
    NTyp        ==== NTyp        = return True
    NLit n0     ==== NLit n1     = return $ n0 == n1
    NProc{}     ==== _           = throwError "(===): TODO NProc"
    _           ==== NProc{}     = throwError "(===): TODO NProc"
    NProto ss0  ==== NProto ss1  = ss0 === ss1
    NAnn{}      ==== _           = throwError "(===): impossible NAnn"
    _           ==== NAnn{}      = throwError "(===): impossible NAnn"
    NFun{}      ==== _           = return False
    NSig{}      ==== _           = return False
    NDef{}      ==== _           = return False
    NTyp        ==== _           = return False
    NLit{}      ==== _           = return False
    NProto{}    ==== _           = return False

instance Conv a => Conv (Arg a) where
  Arg x0 t0 === Arg x1 t1
    | x0 == x1  = t0 === t1
    | otherwise = throwError "(===)/Arg: names are different"

instance Conv a => Conv [a] where
  [] === [] = return True
  (x0:xs0) === (x1:xs1) = x0 === x1 <&&> xs0 === xs1
  _ === _ = return False

instance Conv NSession where
  NEnd       === NEnd       = return True
  NSnd t0 s0 === NSnd t1 s1 = t0 === t1 <&&> s0 === s1
  NRcv t0 s0 === NRcv t1 s1 = t0 === t1 <&&> s0 === s1
  NPar ss0   === NPar ss1   = ss0 === ss1
  NTen ss0   === NTen ss1   = ss0 === ss1
  NEnd       === _          = return False
  NSnd{}     === _          = return False
  NRcv{}     === _          = return False
  NPar{}     === _          = return False
  NTen{}     === _          = return False

-- One has to decide on the meaning of replication: data vs def
-- At least one does not want to expand s^100000
-- So I guess that for now: s^3,s^4 is not convertible to s^7
instance Conv NRSession where
  NRepl s0 t0 === NRepl s1 t1 = s0 === s1 <&&> t0 === t1

instance Conv RSession where
  x === y = if x == y then return True else throwError "Conv RSession: TODO"
-}
-- The error should be in TC
{-
mergeProtos :: Proto -> Proto -> TC Proto
mergeProtos (MkProto p0 (Constraints c0)) (MkProto p1 (Constraints c1))
  = return $ MkProto p (Constraints c)
  where p = Map.mergeWithKey (error "mergeSession") id id p0 p1
        c = Set.union c0 c1
-}

{-
checkConstraints :: Proto -> TC Constraints
checkConstraints p = do
  ks <- asks _chanConstraints -- LENS-ME
  return $ Set.filter ((==ReadyForSplit) . flip constraintStatus p) ks
-}
--  where (ks0, ks1) = Set.partition (`isSubsetOf` k) ks
--
--
-- data Rule = MixRule | SplitRule |
{-
-- TODO here one could compute the freeChans for proc and limit the
-- constraints to those mentioning the free channels of proc.
  ks <- asks _chanConstraints
  let fc0 = freeChans proc
      fc1 = freeChans (Act [] (Procs procs))
--    ks0 = limitConstraintsTo fc0 ks
--    ks1 = limitConstraintsTo fc1 ks
  proto0 <- onConstraints (limitConstraintsTo fc0) $ checkProc proc
  -- ks0   <- checkConstraints proto0
  proto1 <- onConstraints (limitConstraintsTo fc1) $ checkProcs procs
  -- ks1   <- checkConstraints proto1
  let ks0 = proto0 ^. constraints
      ks1 = proto1 ^. constraints
      mks = mergeConstraints ks0 ks1 ks

  debug . concat $
    [ [ "Check procs"
      , "Constraint sets for `" ++ pretty proc ++ "`:"]
    , prettyConstraints ks0
    , [ "Constraint sets for `" ++ pretty (actP [] procs) ++ "':"]
    , prettyConstraints ks1
    , [ "All constraint sets for `" ++ pretty (actP [] (proc:procs)) ++ "':"]
    , prettyConstraints ks
    , [ "Merged constraint sets for `" ++ pretty (actP [] (proc:procs)) ++ "':"]
    , prettyMCCS mks
    ]
  when (countMap (== CSplit) mks > 1) $
    throwError "Wow such splits!"
  when (countMap isCError mks > 1) $
    throwError "Wow such errors!"

  -- The error should be in TC
  let mchans = Map.mergeWithKey (error "mergeSession") id id (proto0 ^. chans) (proto1 ^. chans)
  return $ MkProto mchans ks
{-
  let ks = s2l $ intersection (l2s ks0) (l2s ks1)
      ks' = filter (`elem` proto ^. constraints) ks
  return $
    proto & constraints %~ (ks' ++)
    if ks0 == ks1
    then proto & constraints %~ (ks0 ++)
    else proto
-}
-}
{-
expandDef :: Name -> TC NTerm
expandDef x = do
  me <- asks (\z -> z ^. edefs . at x)
  case me of
    Nothing -> throwError $ "No definition for " ++ unName x
    Just e  -> return e
-}
{-
actConstraints :: Act -> Constraints -> Constraints
actConstraints (Nu c _ d _)  = addConstraint [c,d]
actConstraints (TenOut c ds) = subst1If c ds
actConstraints (ParIn  c ds) = addConstraints [ [d] | d <- ds ] . deleteConstraint [c] . checkAlone c
actConstraints (Send c   _)  = checkAlone c
actConstraints (Recv c _)    = checkAlone c
-}
{-
data Status = SLeft | SRight | SNone -- | SBoth
  deriving (Eq)

instance Print Status where
  prt _ SLeft  = doc $ showString "left"
  prt _ SRight = doc $ showString "right"
  prt _ SNone  = doc $ showString "none"

data Status = Present | Absent
  deriving (Eq)

instance Print Status where
  prt _ Present = doc $ showString "present"
  prt _ Absent  = doc $ showString "absent"

chanStatus :: Proto -> Proto -> Channel -> Status
chanStatus (Proto p0) (Proto p1) c =
  case (p0 ^. at c, p1 ^. at c) of
    (Nothing, Nothing) -> SNone
    (Just _,  Nothing) -> SLeft
    (Nothing, Just  _) -> SRight
    (Just _,  Just  _) -> error "Cannot appear in both sides" -- Both

isMixed' :: [Status'] -> Bool
isMixed' [] = error "isMixed': []"
isMixed' (st:sts) = not $ all (== st) sts

isMixed :: [Status] -> Bool
isMixed [] = error "isMixed: []"
isMixed (st:sts) = not $ all (== st) sts

checkMix :: [Status] -> TC ()
checkMix m
  | SNone `elem` m = error "checkMix: None is part of the mix"
  | otherwise      = return () -- some Left, some Right
  -}
{-
    []   -> return []
    [cs] -> return [cs]
    _    -> return [] -- if
    ks' -> throwError . unlines $ ( "Too many splits!"
                                   : prettyConstraints ks')
    -}

{-
  filter (\cs -> Set.map (chanStatus ) ks
  let statuses = map (Set.map (chanStatus proto)) ks
  return proto
  -}

{-
checkConstraints' :: TC Proto -> TC Proto
checkConstraints' m = do
  proto <- m
  constraints <- asks _chanConstraints
  let mixed = filter isMixed' $ map (map (chanStatus' proto)) constraints
  debug . concat $
    [ ["Checking constraints:"]
    , prettyList constraints
    , ["Concerned protocol:"]
    , prettyProto proto
    , ["Mixed status:"]
    , prettyList mixed
    ]
  case mixed of
    [] ->  return proto -- no mix then mix rule :)
    [m] -> return proto -- one mix then split rule :)
    _   -> throwError "checkConstraints: Wow such mix, much constraints"

checkConstraints :: Proto -> Proto -> TC ()
checkConstraints p0 p1 = do
  constraints <- asks _chanConstraints
  let statuses = map (map (chanStatus p0 p1)) constraints
      mixed    = filter isMixed statuses
  debug . concat $
    [ ["Checking constraints:"]
    , prettyList constraints
    , ["Concerned protocols:"]
    , prettyProto p0
    , ["  *****************************"]
    , prettyProto p1
    , ["Mixed status:"]
    , prettyList mixed
    ]
  case mixed of
    [] ->  return () -- no mix then mix rule :)
    [m] -> checkMix m
    _   -> throwError "checkConstraints: Wow such mix, much constraints"
-}
