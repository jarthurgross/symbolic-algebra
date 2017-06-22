import Op
import Data.Complex.Cyclotomic
import Data.Ratio
import Data.List

b = OpVar "b"
bdg = dag b
c = OpVar "c"
cdg = dag c
h = HermOpVar "H"

rho = HermOpVar "ρ"
sigma = HermOpVar "σ"

sigmaFirst ops = head $ sort $ [ops' | ops' <- (rotations ops),
                                (head ops') == sigma]

sigmaFirstTracesOp op = case op of
  Dag op'      -> dag $ sigmaFirstTracesOp op'
  SMul sca op' -> (sigmaFirstTracesScalar sca) */ (sigmaFirstTracesOp op')
  PowOp op' n  -> PowOp (sigmaFirstTracesOp op') n
  AddOp ops    -> algSum $ map sigmaFirstTracesOp ops
  MulOp ops    -> algProd $ map sigmaFirstTracesOp ops
  op           -> op

sigmaFirstTracesScalar sca = case sca of
  Neg sca'   -> negate $ sigmaFirstTracesScalar sca'
  Conj sca'  -> conjScalar $ sigmaFirstTracesScalar sca'
  Pow sca' n -> Pow (sigmaFirstTracesScalar sca') n
  Abs sca'   -> abs $ sigmaFirstTracesScalar sca'
  Sgn sca'   -> signum $ sigmaFirstTracesScalar sca'
  Tr op      -> Tr $ listToAlg $ map (\(ops, sca') -> (sigmaFirst ops, sca')) $
                listDistributeOp op
  Add scas   -> sum $ map sigmaFirstTracesScalar scas
  Mul scas   -> product $ map sigmaFirstTracesScalar scas
  sca        -> sca

subsFieldExpectsOp op = case op of
  Dag op'      -> dag $ subsFieldExpectsOp op'
  SMul sca op' -> (subsFieldExpectsScalar sca) */ (subsFieldExpectsOp op')
  PowOp op' n  -> PowOp (subsFieldExpectsOp op') n
  AddOp ops    -> algSum $ map subsFieldExpectsOp ops
  MulOp ops    -> algProd $ map subsFieldExpectsOp ops
  op           -> op

subsFieldExpectsScalar sca = case sca of
  Neg sca'   -> negate $ subsFieldExpectsScalar sca'
  Conj sca'  -> conjScalar $ subsFieldExpectsScalar sca'
  Pow sca' n -> Pow (subsFieldExpectsScalar sca') n
  Abs sca'   -> abs $ subsFieldExpectsScalar sca'
  Sgn sca'   -> signum $ subsFieldExpectsScalar sca'
  Tr (HermOpVar "σ") -> Const 1
  Tr (MulOp ((HermOpVar "σ"):ops)) -> Var $ "⟨" ++ (show $ algProd ops) ++ "⟩"
  Add scas   -> sum $ map subsFieldExpectsScalar scas
  Mul scas   -> product $ map subsFieldExpectsScalar scas
  sca        -> sca

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
