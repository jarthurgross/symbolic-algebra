import Op
import Data.Complex.Cyclotomic
import Data.Ratio
import Data.List
import Data.Monoid

a = OpVar "a"
adg = dag a
c = OpVar "c"
cdg = dag c
op00 = OProd (FockVec 0) (FockVec 0)
op11 = OProd (FockVec 1) (FockVec 1)
p0 = op00 /+/ op11
p1 = IdOp /-/ op00 /-/ op11
sqrtgam = RealVar "√γ"
esq = Var "E"
h = (Const (-i / 2)) */ (esq */ (adg /*/ adg) /+/
    (conjScalar $ negate esq) */ (a /*/ a))
l = sqrtgam */ a
k = expandOp $ (Const (-i)) */ h /+/ (Const $ gaussianRat (-1 % 2) 0) */
    (dag l) /*/ l
a_elim = expandOp $ p1 /*/ k /*/ p0 /+/ p0 /*/ k /*/ p1
b_elim = expandOp $ p0 /*/ k /*/ p0
f_elim = expandOp $ l /*/ p1
g_elim = expandOp $ l /*/ p0
nt = HermOpVar "Ñ"
yt = simplifyNt $ ((Const (-2)) * (sqrtgam^^(-2)) ) */ p1 /*/ (nt /-/
     (sqrtgam^^(-2)) */ nt /*/ (esq */ adg /*/ adg /-/
     (conjScalar esq) */ a /*/ a) /*/ nt) /*/ p1
kp = expandOp $ p0 /*/ (b_elim /-/ a_elim /*/ yt /*/ a_elim) /*/ p0

simplifyOpApps :: Op -> Op
simplifyOpApps = converge (==) . (iterate $ expandOp . evalIProdOp .
                                  applyNtOp . applyLadderOp a)

simplifyNt :: Op -> Op
simplifyNt = expandOp . evalIProdOp . (converge (==) .
             (iterate $ expandOp . applyNtOp))

applyNtOp :: Op -> Op
applyNtOp (MulOp ops) = MulOp $ applyNtMulList $ map applyNtOp ops
applyNtOp op = travOpOp applyNtOp op

applyNtMulList :: [Op] -> [Op]
applyNtMulList ops = foldr applyRight [] ops
  where applyRight (PowOp op' m) ((OProd (FockVec n) vec):ops)
          | op' == nt = if n < 2 then [ZeroOp] else
                        (SMul (Const $ sqrtRat $ 1 % n^m)
                         (OProd (FockVec n) vec)):ops
          | otherwise = (PowOp op' m):(OProd (FockVec n) vec):ops
        applyRight (OProd vec (FockVec n)) ((PowOp op' m):ops)
          | op' == nt = if n < 2 then [ZeroOp] else
                        (SMul (Const $ sqrtRat $ 1 % n^m)
                         (OProd vec (FockVec n))):ops
          | otherwise = (OProd (FockVec n) vec):(PowOp op' m):ops
        applyRight op' ((OProd (FockVec n) vec):ops)
          | op' == nt = if n < 2 then [ZeroOp] else
                        (SMul (Const $ sqrtRat $ 1 % n)
                         (OProd (FockVec n) vec)):ops
          | otherwise = op':(OProd (FockVec n) vec):ops
        applyRight (OProd vec (FockVec n)) (op':ops)
          | op' == nt = if n < 2 then [ZeroOp] else
                        (SMul (Const $ sqrtRat $ 1 % n)
                         (OProd vec (FockVec n))):ops
          | otherwise = (OProd vec (FockVec n)):op':ops
        applyRight op ops = op:ops

simplifyLadder :: Op -> Op -> Op
simplifyLadder a = expandOp . evalIProdOp . (converge (==) .
                   (iterate $ expandOp . (applyLadderOp a)))

applyLadderOp :: Op -> Op -> Op
applyLadderOp ladder (MulOp ops) = MulOp $ applyLadderMulList ladder $ map
                                   (applyLadderOp ladder) ops
applyLadderOp ladder op = travOpOp (applyLadderOp ladder) op

-- Would be nice to modify this to pull scalars out separately so chains of
-- ladder operators can be applied without running into scalars.
applyLadderMulList :: Op -> [Op] -> [Op]
applyLadderMulList ladder ops = foldr applyRight [] ops
  where applyRight (PowOp op' m) ((OProd (FockVec n) vec):ops)
          | op' == ladder       = (SMul (Const $ sqrtInteger $
                                         product [n-m+1..n])
                                   (OProd (FockVec (n - m)) vec)):ops
          | op' == (dag ladder) = (SMul (Const $ sqrtInteger $
                                         product [n+1..n+m])
                                   (OProd (FockVec (n + m)) vec)):ops
          | otherwise           = (PowOp op' m):(OProd (FockVec n) vec):ops
        applyRight (OProd vec (FockVec n)) ((PowOp op' m):ops)
          | op' == ladder       = (SMul (Const $ sqrtInteger $
                                         product [n+1..n+m])
                                   (OProd vec (FockVec (n + m)))):ops
          | op' == (dag ladder) = (SMul (Const $ sqrtInteger $
                                         product [n-m+1..n])
                                   (OProd vec (FockVec (n - m)))):ops
          | otherwise           = (OProd (FockVec n) vec):(PowOp op' m):ops
        applyRight op' ((OProd (FockVec n) vec):ops)
          | op' == ladder       = (SMul (Const $ sqrtInteger n)
                                   (OProd (FockVec (n - 1)) vec)):ops
          | op' == (dag ladder) = (SMul (Const $ sqrtInteger (n + 1))
                                   (OProd (FockVec (n + 1)) vec)):ops
          | otherwise           = op':(OProd (FockVec n) vec):ops
        applyRight (OProd vec (FockVec n)) (op':ops)
          | op' == ladder       = (SMul (Const $ sqrtInteger (n + 1))
                                   (OProd vec (FockVec (n + 1)))):ops
          | op' == (dag ladder) = (SMul (Const $ sqrtInteger n)
                                   (OProd vec (FockVec (n - 1)))):ops
          | otherwise           = (OProd vec (FockVec n)):op':ops
        applyRight op ops = op:ops
        applyLeft ((OProd vec (FockVec n)):ops) op'
          | op' == (dag ladder) = (SMul (Const $ sqrtInteger n)
                                   (OProd vec (FockVec (n - 1)))):ops
          | op' == ladder       = (SMul (Const $ sqrtInteger (n + 1))
                                   (OProd vec (FockVec (n + 1)))):ops
          | otherwise           = (OProd vec (FockVec n)):ops
        applyLeft ops op = op:ops

-- Some of the AddOp/MulOp applications could perform some simplifications
-- on-the-fly if I rephrased them as folds with /+/ and /*/.
evalIProdOp :: Op -> Op
evalIProdOp (OProd vec1 vec2) = OProd (evalIProdVec vec1) (evalIProdVec vec2)
evalIProdOp (Dag op) = dag $ evalIProdOp op
evalIProdOp (SMul sca op) = (evalIProdSca sca) */ (evalIProdOp op)
evalIProdOp (PowOp op n) = PowOp (evalIProdOp op) n
evalIProdOp (AddOp ops) = AddOp $ map evalIProdOp ops
evalIProdOp (MulOp ops) = MulOp $ map evalIProdOp ops
evalIProdOp op = op

evalIProdVec :: Vec -> Vec
evalIProdVec (SMulVec sca vec) = (evalIProdSca sca) *| (evalIProdVec vec)
evalIProdVec (LeftAction op vec) = (evalIProdOp op) /*| (evalIProdVec vec)
evalIProdVec (AddVec vecs) = AddVec $ map evalIProdVec vecs
evalIProdVec vec = vec

-- Need to be careful about conjugating scalars in bras. I don't think I'm doing
-- anything wrong in this regard yet, but I haven't specifically checked.
-- Also, haven't bothered with traces in most of these functions.
evalIProdSca :: Scalar -> Scalar
evalIProdSca (IProd (FockVec m) (FockVec n)) = Const (if m == n then 1 else 0)
evalIProdSca (IProd vec1 vec2) = IProd (evalIProdVec vec1) (evalIProdVec vec2)
evalIProdSca (Neg sca) = negate $ evalIProdSca sca
evalIProdSca (Conj sca) = conjScalar $ evalIProdSca sca
evalIProdSca (Pow sca n) = Pow (evalIProdSca sca) n
evalIProdSca (Abs sca) = abs $ evalIProdSca sca
evalIProdSca (Sgn sca) = signum $ evalIProdSca sca
evalIProdSca (Add scas) = sum $ map evalIProdSca scas
evalIProdSca (Mul scas) = product $ map evalIProdSca scas
evalIProdSca sca = sca

-- This currently works when you only have a pattern matching function taking
-- Op to Op. Perhaps it would be worthwhile making a version that accepts a
-- handful of functions for matching patterns on Scalar, Vector, Op, and OpAB.

-- Try and make a function that can traverse an expression tree and apply a
-- specified function mapping Ops to Ops when it matches a pattern. fnOp should
-- check to see if a pattern is matched and do something if so. If the pattern
-- isn't matched it should call travOpOp again. The idea being that this should
-- eliminate a lot of boilerplate code I'm writing.
travOpOp :: (Op -> Op) -> Op -> Op
travOpOp fnOp (OProd vec1 vec2) = OProd (travOpVec fnOp vec1)
                                  (travOpVec fnOp vec2)
travOpOp fnOp (Dag op) = dag (fnOp op)
travOpOp fnOp (SMul sca op) = (travOpSca fnOp sca) */ (fnOp op)
travOpOp fnOp (PowOp op n) = PowOp (fnOp op) n
travOpOp fnOp (TrA op) = TrA (travOpOpAB fnOp op)
travOpOp fnOp (TrB op) = TrB (travOpOpAB fnOp op)
travOpOp fnOp (AddOp ops) = AddOp $ map fnOp ops
travOpOp fnOp (MulOp ops) = MulOp $ map fnOp ops
travOpOp _ op = op
-- I think this is the correct termination condition, since fnOp doesn't
-- terminate when it fails to match, is simply asks travOpOp to drill deeper.
-- Must make sure to call fnOp directly at the high level to ensure fnOp has a
-- chance at matching against the primitives, though.

travOpOpAB :: (Op -> Op) -> OpAB -> OpAB
travOpOpAB fnOp (DagAB op) = dag (travOpOpAB fnOp op)
travOpOpAB fnOp (SMulAB sca op) = (travOpSca fnOp sca) */ (travOpOpAB fnOp op)
travOpOpAB fnOp (PowOpAB op n) = PowOpAB (travOpOpAB fnOp op) n
travOpOpAB fnOp (AddOpAB ops) = AddOpAB $ map (travOpOpAB fnOp) ops
travOpOpAB fnOp (MulOpAB ops) = MulOpAB $ map (travOpOpAB fnOp) ops
travOpOpAB fnOp (TProd op1 op2) = TProd (fnOp op1) (fnOp op2)
travOpOpAB _ op = op

travOpVec :: (Op -> Op) -> Vec -> Vec
travOpVec fnOp (SMulVec sca vec) = (travOpSca fnOp sca) *| (travOpVec fnOp vec)
travOpVec fnOp (LeftAction op vec) = (fnOp op) /*| (travOpVec fnOp vec)
travOpVec fnOp (AddVec vecs) = AddVec $ map (travOpVec fnOp) vecs
travOpVec _ vec = vec

travOpSca :: (Op -> Op) -> Scalar -> Scalar
travOpSca fnOp (IProd vec1 vec2) = IProd (travOpVec fnOp vec1)
                                   (travOpVec fnOp vec2)
travOpSca fnOp (Neg sca) = negate $ travOpSca fnOp sca
travOpSca fnOp (Conj sca) = conjScalar $ travOpSca fnOp sca
travOpSca fnOp (Pow sca n) = Pow (travOpSca fnOp sca) n
travOpSca fnOp (Abs sca) = abs $ travOpSca fnOp sca
travOpSca fnOp (Sgn sca) = signum $ travOpSca fnOp sca
travOpSca fnOp (Tr op) = Tr $ fnOp op
travOpSca fnOp (TrAB op) = TrAB $ travOpOpAB fnOp op
travOpSca fnOp (Add scas) = sum $ map (travOpSca fnOp) scas
travOpSca fnOp (Mul scas) = product $ map (travOpSca fnOp) scas
travOpSca _ sca = sca
