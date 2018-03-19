import AdiabaticElim
import Op
import Data.Complex.Cyclotomic

-- a = OpVar "a"
adg = dag a
c = OpVar "c"
cdg = dag c
op00 = OProd (FockVec 0) (FockVec 0)
op11 = OProd (FockVec 1) (FockVec 1)
p0 = op00 /+/ op11
p1 = IdOp /-/ op00 /-/ op11
sqrtgam = RealVar "√\773γ"
esq = Var "E"

-- These are the strength (r) and phase (ω) of the squeezing for the eigenbasis
-- of the oscillator steady state
cr = RealVar "cosh(r)"
sr = RealVar "sinh(r)"
omega = Var "ω"
l_sq = sqrtgam */ (cr */ a /-/ (omega * sr) */ adg)
h = (Const (-i / 2)) */ (esq */ (adg /*/ adg) /+/
    (conjScalar $ negate esq) */ (a /*/ a))
-- nt = HermOpVar "Ñ"
yt = simplifyNt $ ((Const (-2)) * (sqrtgam^^(-2)) ) */ p1 /*/ (nt /-/
     (sqrtgam^^(-2)) */ nt /*/ (esq */ adg /*/ adg /-/
     (conjScalar esq) */ a /*/ a) /*/ nt) /*/ p1

-- Simplify products of a phase and its conjugate to unity.
collectPhases :: Scalar -> Scalar -> Scalar
collectPhases ph (Mul scas) = (if phase_count > 0 then ph ^ phase_count
                               else if phase_count < 0
                               then (conjScalar ph) ^ (-phase_count)
                               else Const 1) * (product xs)
  where (xs, phase_count) = countPhases ph scas
collectPhases ph sca = travScaSca (collectPhases ph) sca

countPhases :: Scalar -> [Scalar] -> ([Scalar], Integer)
countPhases ph scas = foldr sortPhases ([], 0) scas
  where sortPhases sca@(Pow base n) (scas, phase_count)
          | base == ph            = (scas, phase_count + n)
          | base == conjScalar ph = (scas, phase_count - n)
          | otherwise             = (sca:scas, phase_count)
        sortPhases sca (scas, phase_count)
          | sca == ph            = (scas, phase_count + 1)
          | sca == conjScalar ph = (scas, phase_count - 1)
          | otherwise            = (sca:scas, phase_count)

collectPhasesOp :: Scalar -> Op -> Op
collectPhasesOp ph = travScaOp (collectPhases ph)
