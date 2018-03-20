import Op
import Constant
import AdiabaticElim
import SqueezedBasisElim

-- Tests the consolodation of negations
testConstExpr1 = (CNeg $ CInt 1) * (CNeg $ CRat CI $ CInt 2)

-- Tests consolidating integers, imaginary units, and radicals
testConstExpr2 = (CInt 2) * CI * (CInt 2) * (Sqrt 3) * CI * (Sqrt 2) * CI
