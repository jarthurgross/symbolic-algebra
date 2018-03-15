module AdiabaticElim where

import Op
import Data.Complex.Cyclotomic
import Data.Ratio
import Data.List
import Data.Monoid

k :: Op -> Op -> Op
k h l = expandOp $ (Const (-i)) */ h /+/ (Const $ gaussianRat (-1 % 2) 0) */
        (dag l) /*/ l

a_elim :: Op -> Op -> Op -> Op
a_elim p1 p0 k = expandOp $ p1 /*/ k /*/ p0 /+/ p0 /*/ k /*/ p1

b_elim :: Op -> Op -> Op
b_elim p0 k = expandOp $ p0 /*/ k /*/ p0

f_elim :: Op -> Op -> Op
f_elim p1 l = expandOp $ l /*/ p1

g_elim :: Op -> Op -> Op
g_elim p0 l = expandOp $ l /*/ p0

kp_elim :: Op -> Op -> Op -> Op -> Op
kp_elim p0 b a yt = expandOp $ p0 /*/ (b /-/ a /*/ yt /*/ a) /*/ p0

a = OpVar "a"

simplifyOpApps :: Op -> Op
simplifyOpApps = converge (==) . (iterate $ expandOp . evalIProdOp .
                                  applyNtOp . applyLadderOp a)

nt = HermOpVar "Ñ"

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

-- Do it all again for a function that simplifies scalars sitting within any of
-- these expressions (there still must be a better way to do this...)
travScaOp :: (Scalar -> Scalar) -> Op -> Op
travScaOp fnSca (OProd vec1 vec2) = OProd (travScaVec fnSca vec1)
                                    (travScaVec fnSca vec2)
travScaOp fnSca (Dag op) = dag (travScaOp fnSca op)
travScaOp fnSca (SMul sca op) = (fnSca sca) */ (travScaOp fnSca op)
travScaOp fnSca (PowOp op n) = PowOp (travScaOp fnSca op) n
travScaOp fnSca (TrA op) = TrA (travScaOpAB fnSca op)
travScaOp fnSca (TrB op) = TrB (travScaOpAB fnSca op)
travScaOp fnSca (AddOp ops) = AddOp $ map (travScaOp fnSca) ops
travScaOp fnSca (MulOp ops) = MulOp $ map (travScaOp fnSca) ops
travScaOp _ op = op

travScaOpAB :: (Scalar -> Scalar) -> OpAB -> OpAB
travScaOpAB fnSca (DagAB op) = dag (travScaOpAB fnSca op)
travScaOpAB fnSca (SMulAB sca op) = (fnSca sca) */ (travScaOpAB fnSca op)
travScaOpAB fnSca (PowOpAB op n) = PowOpAB (travScaOpAB fnSca op) n
travScaOpAB fnSca (AddOpAB ops) = AddOpAB $ map (travScaOpAB fnSca) ops
travScaOpAB fnSca (MulOpAB ops) = MulOpAB $ map (travScaOpAB fnSca) ops
travScaOpAB fnSca (TProd op1 op2) = TProd (travScaOp fnSca op1)
                                    (travScaOp fnSca op2)
travScaOpAB _ op = op

travScaVec :: (Scalar -> Scalar) -> Vec -> Vec
travScaVec fnSca (SMulVec sca vec) = (fnSca sca) *| (travScaVec fnSca vec)
travScaVec fnSca (LeftAction op vec) = (travScaOp fnSca op) /*|
                                       (travScaVec fnSca vec)
travScaVec fnSca (AddVec vecs) = AddVec $ map (travScaVec fnSca) vecs
travScaVec _ vec = vec

travScaSca :: (Scalar -> Scalar) -> Scalar -> Scalar
travScaSca fnSca (IProd vec1 vec2) = IProd (travScaVec fnSca vec1)
                                   (travScaVec fnSca vec2)
travScaSca fnSca (Neg sca) = negate $ fnSca sca
travScaSca fnSca (Conj sca) = conjScalar $ fnSca sca
travScaSca fnSca (Pow sca n) = Pow (fnSca sca) n
travScaSca fnSca (Abs sca) = abs $ fnSca sca
travScaSca fnSca (Sgn sca) = signum $ fnSca sca
travScaSca fnSca (Tr op) = Tr $ tracScaOp fnSca op
travScaSca fnSca (TrAB op) = TrAB $ travScaOpAB fnSca op
travScaSca fnSca (Add scas) = sum $ map fnSca scas
travScaSca fnSca (Mul scas) = product $ map fnSca scas
travScaSca _ sca = sca
