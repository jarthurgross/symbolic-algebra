module AdiabaticElim where

import Op
import Constant
import Data.Ratio
import Data.List
import Data.Monoid

i = Const CI

k :: Op -> Op -> Op
k h l = expandOp $ (-i) */ h /+/ (fromRational (-1 % 2)) */
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
                        (SMul (fromRational $ 1 % n^m)
                         (OProd (FockVec n) vec)):ops
          | otherwise = (PowOp op' m):(OProd (FockVec n) vec):ops
        applyRight (OProd vec (FockVec n)) ((PowOp op' m):ops)
          | op' == nt = if n < 2 then [ZeroOp] else
                        (SMul (fromRational $ 1 % n^m)
                         (OProd vec (FockVec n))):ops
          | otherwise = (OProd (FockVec n) vec):(PowOp op' m):ops
        applyRight op' ((OProd (FockVec n) vec):ops)
          | op' == nt = if n < 2 then [ZeroOp] else
                        (SMul (fromRational $ 1 % n)
                         (OProd (FockVec n) vec)):ops
          | otherwise = op':(OProd (FockVec n) vec):ops
        applyRight (OProd vec (FockVec n)) (op':ops)
          | op' == nt = if n < 2 then [ZeroOp] else
                        (SMul (fromRational $ 1 % n)
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
          | op' == ladder       = (SMul (Const $ Sqrt $ product [n-m+1..n])
                                   (OProd (FockVec (n - m)) vec)):ops
          | op' == (dag ladder) = (SMul (Const $ Sqrt $ product [n+1..n+m])
                                   (OProd (FockVec (n + m)) vec)):ops
          | otherwise           = (PowOp op' m):(OProd (FockVec n) vec):ops
        applyRight (OProd vec (FockVec n)) ((PowOp op' m):ops)
          | op' == ladder       = (SMul (Const $ Sqrt $ product [n+1..n+m])
                                   (OProd vec (FockVec (n + m)))):ops
          | op' == (dag ladder) = (SMul (Const $ Sqrt $ product [n-m+1..n])
                                   (OProd vec (FockVec (n - m)))):ops
          | otherwise           = (OProd (FockVec n) vec):(PowOp op' m):ops
        applyRight op' ((OProd (FockVec n) vec):ops)
          | op' == ladder       = (SMul (Const $ Sqrt n)
                                   (OProd (FockVec (n - 1)) vec)):ops
          | op' == (dag ladder) = (SMul (Const $ Sqrt $ n + 1)
                                   (OProd (FockVec (n + 1)) vec)):ops
          | otherwise           = op':(OProd (FockVec n) vec):ops
        applyRight (OProd vec (FockVec n)) (op':ops)
          | op' == ladder       = (SMul (Const $ Sqrt $ n + 1)
                                   (OProd vec $ FockVec $ n + 1)):ops
          | op' == (dag ladder) = (SMul (Const $ Sqrt n)
                                   (OProd vec $ FockVec $ n - 1)):ops
          | otherwise           = (OProd vec $ FockVec n):op':ops
        applyRight op ops = op:ops
        applyLeft ((OProd vec (FockVec n)):ops) op'
          | op' == (dag ladder) = (SMul (Const $ Sqrt n)
                                   (OProd vec $ FockVec $ n - 1)):ops
          | op' == ladder       = (SMul (Const $ Sqrt $ n + 1)
                                   (OProd vec $ FockVec $ n + 1)):ops
          | otherwise           = (OProd vec $ FockVec n):ops
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
