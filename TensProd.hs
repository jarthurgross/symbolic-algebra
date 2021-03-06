module TensProd
( Scalar(..)
, OpAB(..)
, Op(..)
) where

import Data.Ratio
import Data.List
import qualified Data.Map as Map

c = OpVar "c"
b = OpVar "b"
rho = OpVar "ρ"
sigma = OpVar "σ"

u = (TProd Id Id) /+/ (sqrtdt */
    ((TProd c $ Dag b) /+/ ((-1) */ (TProd (Dag c) b)))) /+/
    (((sqrtdt * sqrtdt) * (SConst $ 1%2)) */
    (((TProd c $ Dag b) /+/ ((-1) */ (TProd (Dag c) b))) /*/
    ((TProd c $ Dag b) /+/ ((-1) */ (TProd (Dag c) b)))))

x = SVar "x"
y = SVar "y"
sqrtdt = SVar "√Δ𝜏"

sExpr = MulS [AddS [x, 1], AddS[y, MulS [x, y]], 5]

-- This module is supposed to model a twofold tensor product space of two
-- identified algebras.

-- It's currently kind of a mess. The simplification flow I have in mind is
--     canonicizeScalars $ collectScalars $ standardizeScalars $ expand expr
-- to get things in a somewhat canonical form.
simplify :: Op -> Op
simplify = cleanupOp . canonicizeScalars . collectScalars . standardizeScalars .
           expand

-- This guy should take an Op that is a sum of terms that are products of
-- scalars and a product of Ops, where the Ops in these products contain no
-- sums, no scalar multiplications, and no further products. Furthermore, any
-- OpABs inside partial traces should conform to the same pattern (a single
-- product of OpABs with no internal sums, scalar multiplications, or products).
-- As it is, there seems to be some inconsistency with how I handle products
-- with only one factor. Sometimes they are simplified to the Op(AB) without the
-- wrapping product, and sometimes they are left in the product. I should
-- probably standardize this.
canonicizeScalars :: Op -> Op
canonicizeScalars (AddOp ops) = AddOp $ map canonicizeScalars ops
canonicizeScalars (SMul s op) = SMul (constantCollect $ scalarArrProd $
                                scalarExpand $ pushDownNeg s) op
canonicizeScalars op = op

pushDownNeg :: Scalar -> Scalar
pushDownNeg (SNeg s) = case s of
  SConst r     -> SConst (-r)
  AddS ss      -> AddS $ map (pushDownNeg . SNeg) ss
  MulS (s':ss) -> MulS $ (pushDownNeg $ SNeg s'):ss
  SNeg s'      -> pushDownNeg s'
  SInv s'      -> SInv $ pushDownNeg $ SNeg s'
pushDownNeg (AddS ss) = AddS $ map pushDownNeg ss
pushDownNeg (MulS ss) = MulS $ map pushDownNeg ss
pushDownNeg (SInv s) = SInv $ pushDownNeg s
pushDownNeg (Abs (SNeg s)) = pushDownNeg (Abs s)
pushDownNeg (Abs s) = Abs $ pushDownNeg s
pushDownNeg s = s

scalarExpand :: Scalar -> Scalar
scalarExpand = AddS . (map MulS) . scalarExpand'
  where scalarExpand' (AddS ss) = concat $ map scalarExpand' ss
        scalarExpand' (MulS ss) = map concat $ sequence $ map scalarExpand' ss
        scalarExpand' s = [[s]]

-- This function assumes we have a sum of products of scalars (with no further
-- sums or products). It is meant to sort the products so the constant is in
-- front and the variables are arranged alphabetically.
scalarArrProd :: Scalar -> Scalar
scalarArrProd (AddS ss) = AddS $ map scalarArrProd ss
scalarArrProd (MulS ss) = MulS $ scalarArrProd' ss
scalarArrProd s = s

-- Scalar symbols are crudely sorted by their show strings.
scalarArrProd' :: [Scalar] -> [Scalar]
scalarArrProd' factors = (SConst $ product cs):(sortOn show ss)
  where collectConsts (SConst c) acc = (c:(fst acc), snd acc)
        collectConsts s acc = (fst acc, s:(snd acc))
        (cs, ss) = foldr collectConsts ([], []) factors

-- Assumes products have single constant term which appears at beginning and
-- the variable terms are sorted canonically.
constantCollect :: Scalar -> Scalar
constantCollect (AddS ss) = AddS $ map (\(k, v) -> MulS $ (SConst $ sum v):k)
                            collectedPairs
  where collectedPairs = Map.toList $ Map.fromListWith (++) pairs
        pairs = foldr (\x acc -> (constProdPair x):acc) [] ss
        constProdPair (MulS ((SConst c):ss')) = (ss', [c])
        constProdPair (MulS ss') = (ss', [1 % 1])
        constProdPair s = ([s], [1 % 1])

-- The OpAB in the list shouldn't have any AddAB terms (consider using
-- LiquidHaskell to enforce this)
raiseSumsList :: OpAB -> [OpAB]
raiseSumsList (MulAB ops) = map MulAB $ sequence $ map raiseSumsList ops
raiseSumsList (AddAB ops) = concat $ map raiseSumsList ops
raiseSumsList (SMulAB s op) = map (SMulAB s) $ raiseSumsList op
raiseSumsList op = [op]

-- The OpAB here shouldn't have any sums (again, consider refinement types)
-- For now we just consider sums and commutators as atoms
separateScalars :: OpAB -> ([Scalar], [OpAB])
separateScalars (SMulAB s op) = (s:ss, ops)
  where (ss, ops) = separateScalars op
separateScalars (MulAB ops) = concatPairLists $ map separateScalars ops
  where concatPairLists = foldr (\(s1s, op1s) (s2s, op2s) ->
                          (s1s ++ s2s, op1s ++ op2s)) ([], [])
separateScalars op = ([], [op])

canonPartTrace :: Op -> Op
canonPartTrace (TraceA op) = AddOp $ map (\(ss, ops) -> SMul (MulS ss)
                             (TraceA $ MulAB ops)) $ map separateScalars $
                             raiseSumsList op
canonPartTrace (TraceB op) = AddOp $ map (\(ss, ops) -> SMul (MulS ss)
                             (TraceB $ MulAB ops)) $ map separateScalars $
                             raiseSumsList op
canonPartTrace op = op

class (Eq a) => Algebra a where
  (/+/) :: a -> a -> a
  (/*/) :: a -> a -> a
  (*/) :: Scalar -> a -> a
  comm :: a -> a -> a
  trace :: a -> Scalar
  expand :: a -> a
  expand = id
  distributeScalars :: a -> a
  distributeScalars = id
  standardizeScalars :: a -> a
  standardizeScalars = id
  collectScalars :: a -> a
  collectScalars = id
  simplifyScalars :: a -> a
  simplifyScalars = id

-- Applies a function repeatedly until the last two function applications
-- satisfy some convergence criterion, returning the last function application.
-- Taken from http://stackoverflow.com/a/7443379/1236650
converge :: (a -> a -> Bool) -> [a] -> a
converge p (x:ys@(y:_))
  | p x y     = y
  | otherwise = converge p ys

instance Algebra Op where
  (AddOp ops) /+/ op = AddOp (ops ++ [op])
  op /+/ (AddOp ops) = AddOp (op:ops)
  op1 /+/ op2 = AddOp [op1, op2]
  (MulOp ops) /*/ op = MulOp (ops ++ [op])
  op /*/ (MulOp ops) = MulOp (op:ops)
  op1 /*/ op2 = MulOp [op1, op2]
  s1 */ (SMul s2 op) = SMul (s1 * s2) op
  s */ op = SMul s op
  comm op1 op2 = Comm op1 op2
  trace op = Trace op

  expand = AddOp . (map MulOp) . expand' . distributeScalars . pushDownDag
    -- expand' makes a list of lists of ops, where the interior lists represent
    -- products and the exterior list represents a sum
    where expand' (AddOp ops) = concat $ map expand' ops
          expand' (SMul s (MulOp (op:ops))) = expand' $ MulOp $
                                              (distributeScalars $ SMul s op):
                                              ops
          expand' (MulOp ops) = map concat (sequence $ map expand' ops)
          expand' op          = [[op]]

  distributeScalars op = case op of
    SMul s (AddOp ops) -> AddOp $ map (distributeScalars . (SMul s)) ops
    AddOp ops          -> AddOp $ map distributeScalars ops
    MulOp ops          -> MulOp $ map distributeScalars ops
    Comm op1 op2       -> Comm (distributeScalars op1) (distributeScalars op2)
    op                 -> op

  standardizeScalars = converge (==) . iterate standardizeScalars'
    where standardizeScalars' op = case op of
            SMul s (SMul s' op')  -> SMul (MulS [s, s']) $
                                     standardizeScalars' op'
            SMul s (AddOp ops)    -> AddOp $ map (SMul s)
                                     (map standardizeScalars' ops)
            SMul s op'            -> SMul s $ standardizeScalars' op'
            MulOp ops             -> if ss == []
                                     then MulOp $ map standardizeScalars' ops
                                     else SMul (MulS ss)
                                          (MulOp $ map standardizeScalars' ops')
              where collectScalar (SMul s op') acc = (s:(fst acc),
                                                     op':(snd acc))
                    collectScalar op' acc = (fst acc, op':(snd acc))
                    (ss, ops') = foldr collectScalar ([], []) ops
            AddOp ops             -> AddOp $ map standardizeScalars' ops
            TraceA (SMulAB s op') -> SMul s (TraceA (standardizeScalars op'))
            TraceB (SMulAB s op') -> SMul s (TraceB (standardizeScalars op'))
            TraceA op'            -> TraceA (standardizeScalars op')
            TraceB op'            -> TraceB (standardizeScalars op')
            Comm (SMul s op1) op2 -> SMul s (Comm (standardizeScalars' op1)
                                     (standardizeScalars' op2))
            Comm op1 (SMul s op2) -> SMul s (Comm (standardizeScalars' op1)
                                     (standardizeScalars' op2))
            Comm op1 op2          -> Comm (standardizeScalars' op1)
                                     (standardizeScalars' op2)
            op                    -> op

  -- Consider writing with aggregateAL:
  -- http://hackage.haskell.org/package/hinduce-missingh-0.0.0.0/docs/Data-List-HIUtils.html#v%3aaggregateAL
  collectScalars (AddOp ops) = AddOp $ map (\(k, v) -> SMul (AddS v) k)
                               collectedPairs
    where collectedPairs = Map.toList $ Map.fromListWith (++) pairs
          pairs = foldr (\x acc -> (scalOpPair x):acc) [] ops
          scalOpPair (SMul s op) = (op, [s])
          scalOpPair op          = (op, [SConst 1])

  simplifyScalars = simplifyScalars' . collectScalars . standardizeScalars
    where simplifyScalars' (SMul s op) = SMul
                                         (collectConsts $ expandScalar s) op
          simplifyScalars' (AddOp ops) = AddOp $ map simplifyScalars' ops
          -- The below is kind of weird, since I am only applying
          -- simplifyScalars' after collectScalars, so there shouldn't be any
          -- scalars left in the operator product.
          -- Also I plan to call this after expand, so the only SMuls should be
          -- inside the first (and only) AddOp, so much of the following could
          -- be eliminated if I restrict myself to that use case.
          simplifyScalars' (MulOp ops) = MulOp $ map simplifyScalars' ops
          simplifyScalars' (Comm op1 op2) = Comm (simplifyScalars' op1)
                                            (simplifyScalars' op2)
          simplifyScalars' op = op

instance Algebra OpAB where
  (AddAB ops) /+/ op = AddAB (ops ++ [op])
  op /+/ (AddAB ops) = AddAB (op:ops)
  op1 /+/ op2 = AddAB [op1, op2]
  (MulAB ops) /*/ op = MulAB (ops ++ [op])
  op /*/ (MulAB ops) = MulAB (op:ops)
  op1 /*/ op2 = MulAB [op1, op2]
  s1 */ (SMulAB s2 op) = SMulAB (s1 * s2) op
  s */ op = SMulAB s op
  comm op1 op2 = CommAB op1 op2
  trace op = TraceAB op

  distributeScalars op = case op of
    SMulAB s (AddAB ops) -> AddAB $ map (distributeScalars . (SMulAB s)) ops
    AddAB ops            -> AddAB $ map distributeScalars ops
    MulAB ops            -> MulAB $ map distributeScalars ops
    CommAB op1 op2       -> CommAB (distributeScalars op1)
                            (distributeScalars op2)
    op                   -> op

  expand = AddAB . (map MulAB) . expand' . distributeScalars . pushDownDagAB
    -- expand' makes a list of lists of ops, where the interior lists represent
    -- products and the exterior list represents a sum
    where expand' (AddAB ops) = concat $ map expand' ops
          expand' (MulAB ops) = map concat $ sequence $ map expand' ops
          expand' (SMulAB s (MulAB (op:ops))) = expand' $ MulAB $
                                                (distributeScalars $
                                                SMulAB s op):ops
          expand' op = [[op]]

  -- This function looks like a mess, but it does seem to distribute the
  -- scalars, pull them out from inside traces and commutators, and collect them
  -- to the left of operator products. I may be able to find a way to make this
  -- more elegant, though.
  standardizeScalars = converge (==) . iterate standardizeScalars'
    where standardizeScalars' op = case op of
            SMulAB s (SMulAB s' op')  -> SMulAB (MulS [s, s']) $
                                         standardizeScalars' op'
            SMulAB s (AddAB ops)      -> AddAB $ map (SMulAB s)
                                         (map standardizeScalars' ops)
            SMulAB s op'              -> SMulAB s $ standardizeScalars' op'
            MulAB ops                 -> if ss == []
                                         then MulAB $
                                              map standardizeScalars' ops
                                         else SMulAB (MulS ss) (MulAB $
                                              map standardizeScalars' ops')
              where collectScalar (SMulAB s op') acc = (s:(fst acc),
                                                       op':(snd acc))
                    collectScalar op' acc = (fst acc, op':(snd acc))
                    (ss, ops') = foldr collectScalar ([], []) ops
            AddAB ops                 -> AddAB $ map standardizeScalars' ops
            CommAB (SMulAB s op1) op2 -> SMulAB s (CommAB
                                         (standardizeScalars' op1)
                                         (standardizeScalars' op2))
            CommAB op1 (SMulAB s op2) -> SMulAB s (CommAB
                                         (standardizeScalars' op1)
                                         (standardizeScalars' op2))
            CommAB op1 op2            -> CommAB (standardizeScalars' op1)
                                         (standardizeScalars' op2)
            op                        -> op

simpTProd :: OpAB -> OpAB
simpTProd (SMulAB s op) = SMulAB s $ simpTProd op
simpTProd (DagAB op) = DagAB $ simpTProd op
simpTProd (AddAB ops) = AddAB $ map simpTProd ops
simpTProd (MulAB ops) = MulAB $ simpTPMulList ops
simpTProd (CommAB op1 op2) = CommAB (simpTProd op1) (simpTProd op2)

simpTPMulList :: [OpAB] -> [OpAB]
simpTPMulList ((TProd opA1 opB1):(TProd opA2 opB2):ops) =
  simpTPMulList $ (TProd (simplify $ MulOp [opA1, opA2])
  (simplify $ MulOp [opB1, opB2])):ops
simpTPMulList (op1:op2:ops) = op1:(simpTPMulList $ op2:ops)
simpTPMulList ops = ops

simplifyAB :: OpAB -> OpAB
simplifyAB = cleanupAB . simpTProd . canonicizeScalarsAB . collectScalars .
  standardizeScalars . expand

-- Remove a bunch of overly cumbersome constructs we built in the simplification
-- process, e.g. products/sums of singleton lists and trivial multiplications.
cleanupOp :: Op -> Op
cleanupOp (TraceA op) = TraceA $ cleanupAB op
cleanupOp (TraceB op) = TraceB $ cleanupAB op
cleanupOp (Dag op) = Dag $ cleanupOp op
cleanupOp (SMul s op) = cleanupSMul (cleanupScalar s) (cleanupOp op)
cleanupOp (AddOp (op:[])) = cleanupOp op
cleanupOp (AddOp ops) = AddOp $ map cleanupOp ops
cleanupOp (MulOp (op:[])) = cleanupOp op
cleanupOp (MulOp ops) = MulOp $ cleanupMulListOp $ map cleanupOp ops
cleanupOp op = op

cleanupMulListOp :: [Op] -> [Op]
cleanupMulListOp (Id:op:ops) = cleanupMulListOp $ op:ops
cleanupMulListOp (op:Id:ops) = cleanupMulListOp $ op:ops
cleanupMulListOp (op:ops) = (cleanupOp op):(cleanupMulListOp ops)
cleanupMulListOp [] = []

cleanupSMul :: Scalar -> Op -> Op
cleanupSMul 1 op = op
cleanupSMul s op = SMul s op

cleanupAB :: OpAB -> OpAB
cleanupAB (TProd op1 op2) = TProd (cleanupOp op1) (cleanupOp op2)
cleanupAB (DagAB op) = DagAB $ cleanupAB op
cleanupAB (SMulAB s op) = cleanupSMulAB (cleanupScalar s) (cleanupAB op)
cleanupAB (AddAB (op:[])) = cleanupAB op
cleanupAB (AddAB ops) = AddAB $ map cleanupAB ops
cleanupAB (MulAB (op:[])) = cleanupAB op
cleanupAB (MulAB ops) = MulAB $ cleanupMulListAB $ map cleanupAB ops
cleanupAB op = op

cleanupSMulAB :: Scalar -> OpAB -> OpAB
cleanupSMulAB 1 op = op
cleanupSMulAB s op = SMulAB s op

cleanupScalar :: Scalar -> Scalar
cleanupScalar (AddS (s:[])) = cleanupScalar s
cleanupScalar (MulS (s:[])) = cleanupScalar s
cleanupScalar (MulS ss) = MulS $ cleanupMulListScalar ss
cleanupScalar s = s

-- We're handling the multiplicative identity, but we should also be handling
-- the additive identity (will need to add the zero operator).

cleanupMulListScalar :: [Scalar] -> [Scalar]
cleanupMulListScalar (1:s:ss) = cleanupMulListScalar $ s:ss
cleanupMulListScalar (s:1:ss) = cleanupMulListScalar $ s:ss
cleanupMulListScalar (s:ss) = (cleanupScalar s):(cleanupMulListScalar ss)
cleanupMulListScalar [] = []

cleanupMulListAB :: [OpAB] -> [OpAB]
cleanupMulListAB (IdAB:op:ops) = cleanupMulListAB $ op:ops
cleanupMulListAB (op:IdAB:ops) = cleanupMulListAB $ op:ops
cleanupMulListAB (op:ops) = (cleanupAB op):(cleanupMulListAB ops)
cleanupMulListAB [] = []

canonicizeScalarsAB :: OpAB -> OpAB
canonicizeScalarsAB (AddAB ops) = AddAB $ map canonicizeScalarsAB ops
canonicizeScalarsAB (SMulAB s op) = SMulAB (constantCollect $ scalarArrProd $
                                    scalarExpand $ pushDownNeg s) op
canonicizeScalarsAB op = op

-- In the future, consider using cyclotomic numbers for SConst, implemented in
-- package Data.Complex.Cyclotomic
data Scalar = Trace Op
            | TraceAB OpAB
            | SVar String
            | SConst Rational
            | AddS [Scalar]
            | MulS [Scalar]
            | SNeg Scalar
            | SInv Scalar
            | Abs Scalar deriving (Eq, Ord)

instance Num Scalar where
  s1 + s2 = AddS [s1, s2]
  s1 * s2 = MulS [s1, s2]
  abs s = Abs s
  signum s = MulS [SInv (Abs s), s]
  fromInteger = SConst . fromInteger
  negate s = SNeg s

expandScalar :: Scalar -> Scalar
expandScalar = AddS . (map MulS) . expandScalar'
  where expandScalar' (AddS ss) = concat $ map expandScalar' ss
        expandScalar' (MulS ss) = map concat $ sequence $ map expandScalar' ss
        expandScalar' s = [[s]]

-- This function currently has a problem if one of the factors in a product is
-- itself a product. This isn't an issue if expandScalar is called first, as it
-- never has products inside products, but some thought should be given to this.
collectConsts :: Scalar -> Scalar
collectConsts (MulS ss) = joinConstVar constVarList
  where joinConstVar ([], []) = SConst 1
        joinConstVar ([], vs) = MulS vs
        joinConstVar (cs, vs) = MulS $ (SConst $ foldr (*) 1 cs):vs
        constVarList = foldr separateConsts ([], []) $ map collectConsts ss
        separateConsts (SConst c) (cs, vs) = (c:cs, vs)
        separateConsts v (cs, vs) = (cs, v:vs)
collectConsts (AddS ss) = AddS $ map collectConsts ss
collectConsts (SNeg s) = SNeg $ collectConsts s
collectConsts (SInv s) = SInv $ collectConsts s
collectConsts (Abs s) = Abs $ collectConsts s
collectConsts s = s

traceA :: OpAB -> Op
traceA op = TraceA op

traceB :: OpAB -> Op
traceB op = TraceB op

(><) :: Op -> Op -> OpAB
op1 >< op2 = TProd op1 op2

data Op = TraceA OpAB
        | TraceB OpAB
        | OpVar String
        | Id
        | Dag Op
        | SMul Scalar Op
        | AddOp [Op]
        | MulOp [Op]
        | Comm Op Op deriving (Eq, Ord)

data OpAB = TProd Op Op
          | SMulAB Scalar OpAB
          | OpABVar String
          | IdAB
          | DagAB OpAB
          | AddAB [OpAB]
          | MulAB [OpAB]
          | CommAB OpAB OpAB deriving (Eq, Ord)

-- Note: our scalars are currently all real
pushDownDagAB :: OpAB -> OpAB
pushDownDagAB (DagAB op) = case op of
  TProd op1 op2  -> TProd (pushDownDag $ Dag op1) (pushDownDag $ Dag op2)
  SMulAB s op'   -> SMulAB s $ pushDownDagAB $ DagAB op'
  OpABVar s      -> DagAB $ OpABVar s
  IdAB           -> IdAB
  DagAB op'      -> pushDownDagAB op'
  AddAB ops      -> AddAB $ map (pushDownDagAB . DagAB) ops
  MulAB ops      -> MulAB $ map (pushDownDagAB . DagAB) $ reverse ops
  CommAB op1 op2 -> CommAB (pushDownDagAB $ DagAB op1)
                    (pushDownDagAB $ DagAB op2)
pushDownDagAB (TProd op1 op2) = TProd (pushDownDag op1) (pushDownDag op2)
pushDownDagAB (SMulAB s op) = SMulAB s $ pushDownDagAB op
pushDownDagAB (OpABVar s) = OpABVar s
pushDownDagAB IdAB = IdAB
pushDownDagAB (AddAB ops) = AddAB $ map pushDownDagAB ops
pushDownDagAB (MulAB ops) = MulAB $ map pushDownDagAB ops
pushDownDagAB (CommAB op1 op2) = CommAB (pushDownDagAB op1) (pushDownDagAB op2)

pushDownDag :: Op -> Op
pushDownDag (Dag op) = case op of
  TraceA op'   -> TraceA $ pushDownDagAB $ DagAB op'
  TraceB op'   -> TraceB $ pushDownDagAB $ DagAB op'
  OpVar s      -> Dag $ OpVar s
  Id           -> Id
  Dag op'      -> pushDownDag op'
  SMul s op'   -> SMul s $ pushDownDag $ Dag op'
  AddOp ops    -> AddOp $ map (pushDownDag . Dag) ops
  MulOp ops    -> MulOp $ map (pushDownDag . Dag) $ reverse ops
  Comm op1 op2 -> Comm (pushDownDag $ Dag op1) (pushDownDag $ Dag op2)
pushDownDag (TraceA op) = TraceA $ pushDownDagAB op
pushDownDag (TraceB op) = TraceB $ pushDownDagAB op
pushDownDag (OpVar s) = OpVar s
pushDownDag Id = Id
pushDownDag (SMul s op) = SMul s $ pushDownDag op
pushDownDag (AddOp ops) = AddOp $ map pushDownDag ops
pushDownDag (MulOp ops) = MulOp $ map pushDownDag ops
pushDownDag (Comm op1 op2) = Comm (pushDownDag op1) (pushDownDag op2)

instance Show Scalar where
  show (Trace op) = showTrace "" op
  show (TraceAB op) = showTrace "" op
  show (SVar s) = s
  show (SConst r)
    | d == 1    = show n
    | otherwise = "(" ++ (show n) ++ "/" ++ (show d) ++ ")"
    where d = denominator r
          n = numerator r
  show (AddS xs) = showAssoc " + " xs
  show (MulS xs) = showAssoc "⋅" xs
  show (SNeg s) = "−" ++ (show s)
  show (SInv s) = (show s) ++ "⁻¹"
  show (Abs s) = "|" ++ (show s) ++ "|"

instance Show Op where
  show (TraceA op) = showTrace "ᴬ" op
  show (TraceB op) = showTrace "ᴮ" op
  show (OpVar s) = s
  show Id = "𝟙"
  show (Dag op) = (show op) ++ "*"
  show (SMul s op) = (show s) ++ "⋅" ++ (show op)
  show (AddOp xs) = showAssoc " + " xs
  show (MulOp xs) = showAssoc "⋅" xs
  show (Comm op1 op2) = showComm op1 op2

instance Show OpAB where
  show (TProd op1 op2) = (show op1) ++ "⊗" ++ (show op2)
  show (SMulAB s op) = (show s) ++ "⋅" ++ (show op)
  show (OpABVar s) = s ++ "ᴬᴮ"
  show IdAB = "𝟙ᴬᴮ"
  show (DagAB op) = (show op) ++ "*"
  show (AddAB xs) = showAssoc " + " xs
  show (MulAB xs) = showAssoc "⋅" xs
  show (CommAB op1 op2) = showComm op1 op2

showTrace :: (Show a) => String -> a -> String
showTrace dec x = "Tr" ++ dec ++ "[" ++ (show x) ++ "]"

showAssoc :: (Show a) => String -> [a] -> String
showAssoc op xs = "(" ++ (showAssoc' op xs) ++ ")"

showAssoc' :: (Show a) => String -> [a] -> String
showAssoc' op (x:y:zs) = (show x) ++ op ++ (showAssoc' op (y:zs))
showAssoc' _ (x:[]) = show x
showAssoc' _ [] = ""

showComm :: (Show a) => a -> a -> String
showComm x y = "[" ++ (show x) ++ ", " ++ (show y) ++ "]"
