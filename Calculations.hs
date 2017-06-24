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

phase = Var "ω"

supOpD :: Algebra a => a -> a -> a
supOpD c x = c /*/ x /*/ (dag c) /+/ (negate half) */
             ((dag c) /*/ c /*/ x /+/ x /*/ (dag c) /*/ c)

n = RealVar "N"
nth = Const 0
-- nth = RealVar "Nₜₕ"
m = Var "M"

l' = 2 * n + m + (conjScalar m) + 1

csq = (conjScalar phase) */ ((nth + n + (conjScalar m) + 1) */ c /+/
      (nth - n - m) */ (dag c))

cr = RealVar "coshr"
sr = RealVar "sinhr"

csq' = cr */ c /+/ (phase * sr) */ cdg

supOpDcsq' = (cr^2) */ (supOpD c rho) /+/ (sr^2) */ (supOpD cdg rho) /+/
             (-half * (conjScalar phase) * cr * sr) */ (comm c $ comm c rho) /+/
             (-half * phase * cr * sr) */ (comm cdg $ comm cdg rho)

comm :: Algebra a => a -> a -> a
comm a b = a /*/ b /+/ (-1) */ b /*/ a

supOpDcsqCandidate = l' */ ((n + nth + 1) */ (supOpD c rho) /+/
                     (n + (-1) * nth) */ (supOpD (dag c) rho) /+/
                     (half * (conjScalar m)) */ (comm c $ comm c rho) /+/
                     (half * m) */ (comm (dag c) $ comm (dag c) rho))

simplifyPhaseScalar :: Scalar -> Scalar
simplifyPhaseScalar (Neg sca) = negate $ simplifyPhaseScalar sca
simplifyPhaseScalar (Conj sca) = conjScalar $ simplifyPhaseScalar sca
simplifyPhaseScalar (Pow sca n) = Pow (simplifyPhaseScalar sca) n
simplifyPhaseScalar (Abs sca) = abs $ simplifyPhaseScalar sca
simplifyPhaseScalar (Sgn sca) = signum $ simplifyPhaseScalar sca
simplifyPhaseScalar (Tr op) = Tr $ simplifyPhaseOp op
simplifyPhaseScalar (TrAB op) = TrAB $ simplifyPhaseOpAB op
simplifyPhaseScalar (Add scas) = sum $ map simplifyPhaseScalar scas
simplifyPhaseScalar (Mul scas) = product $ cancelPhases $
                                 map simplifyPhaseScalar scas
simplifyPhaseScalar sca = sca

cancelPhases :: [Scalar] -> [Scalar]
cancelPhases scas = nonPhases ++ if balance > 0 then replicate balance phase
                    else replicate (-balance) $ conjScalar phase
  where balance = (length phases) - (length conjPhases)
        phases = [sca | sca <- scas, sca == phase]
        conjPhases = [sca | sca <- scas, sca == conjScalar phase]
        nonPhases = [sca | sca <- scas, sca /= phase && sca /= conjScalar phase]

simplifyPhaseOp :: Op -> Op
simplifyPhaseOp (Dag op) = dag $ simplifyPhaseOp op
simplifyPhaseOp (SMul sca op) = (simplifyPhaseScalar sca) */
                                (simplifyPhaseOp op)
simplifyPhaseOp (PowOp op n) = PowOp (simplifyPhaseOp op) n
simplifyPhaseOp (TrA op) = TrA $ simplifyPhaseOpAB op
simplifyPhaseOp (TrB op) = TrB $ simplifyPhaseOpAB op
simplifyPhaseOp (AddOp ops) = algSum $ map simplifyPhaseOp ops
simplifyPhaseOp (MulOp ops) = algProd $ map simplifyPhaseOp ops
simplifyPhaseOp op = op

simplifyPhaseOpAB :: OpAB -> OpAB
simplifyPhaseOpAB (DagAB op) = dag $ simplifyPhaseOpAB op
simplifyPhaseOpAB (SMulAB sca op) = (simplifyPhaseScalar sca) */
                                    (simplifyPhaseOpAB op)
simplifyPhaseOpAB (PowOpAB op n) = PowOpAB (simplifyPhaseOpAB op) n
simplifyPhaseOpAB (AddOpAB ops) = algSum $ map simplifyPhaseOpAB ops
simplifyPhaseOpAB (MulOpAB ops) = algProd $ map simplifyPhaseOpAB ops
simplifyPhaseOpAB (TProd opa opb) = TProd (simplifyPhaseOp opa)
                                    (simplifyPhaseOp opb)
simplifyPhaseOpAB op = op
