import Op
import Data.Complex.Cyclotomic
import Data.Ratio

b = OpVar "b"
bdg = dag b
c = OpVar "c"
cdg = dag c
h = HermOpVar "H"

rho = HermOpVar "ρ"
sigma = HermOpVar "σ"

x = Var "x"
y = Var "y"

u = IdOp /+/ (SMul (Const $ e 4) h) /+/ (SMul (Const (-1/2)) (h /*/ h))

ui = IdOpAB /+/ sqrtdt */ (c >< bdg /-/ (cdg >< b)) /+/
     (half * sqrtdt * sqrtdt) */ (c >< bdg /-/ cdg >< b) /*/ (c >< bdg /-/ cdg >< b)

sqrtdt = RealVar "√\0773Δ\0773τ"
half = Const $ gaussianRat (1 % 2) 0

bout = collectOnB $ normalOrderB b $ truncateToOrderOpAB sqrtdt 3 $
       (dag ui) /*/ (IdOp >< b) /*/ ui

boutdagbout = collectOnB $ truncateToOrderOpAB sqrtdt 3 $ (dag bout) /*/ bout

ket0 = VecVar "0"
ket1 = VecVar "1"
