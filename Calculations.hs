import Op
import Data.Complex.Cyclotomic
import Data.Ratio

a = OpVar "A"
b = OpVar "b"
bdg = dag b
c = OpVar "c"
cdg = dag c
h = HermOpVar "H"

x = Var "x"
y = Var "y"

u = IdOp /+/ (SMul (Const $ e 4) h) /+/ (SMul (Const (-1/2)) (h /*/ h))

ui = IdOpAB /+/ sqrtdt */ (c >< bdg /-/ (cdg >< b)) /+/
     (half * sqrtdt * sqrtdt) */ (c >< bdg /-/ cdg >< b) /*/ (c >< bdg /-/ cdg >< b)

sqrtdt = RealVar "√\0773Δ\0773τ"
half = Const $ gaussianRat (1 % 2) 0
