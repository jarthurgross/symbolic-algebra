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
sqrtgam = RealVar "√γ"
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

-- simplifyPhaseMag :: Scalar -> Scalar
-- TODO: Write a function that simplifies products of the phase with it's
-- conjugate to
-- 1.
