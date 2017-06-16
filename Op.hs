-- Start again with operator algebra, trying to make things more streamlined

import Data.List
import Data.Complex.Cyclotomic

a = OpVar "A"
b = OpVar "B"
h = HermOpVar "H"

x = Var "x"
y = Var "y"

u = IdOp /+/ (SMul (Const $ e 4) h) /+/ (SMul (Const (-1/2)) (h /*/ h))

data Scalar = Const Cyclotomic
            | Var String
            | RealVar String
            | Neg Scalar
            | Conj Scalar
            | Pow Scalar Integer
            | Abs Scalar
            | Sgn Scalar
            | Add [Scalar]
            | Mul [Scalar] deriving (Eq, Ord)

data Op = ZeroOp
        | IdOp
        | OpVar String
        | HermOpVar String
        | Dag Op
        | SMul Scalar Op
        | PowOp Op Integer
        | AddOp [Op]
        | MulOp [Op] deriving (Eq, Ord)

data OpAB = ZeroOpAB
          | IdOpAB
          | OpABVar String
          | HermOpABVar String
          | DagAB OpAB
          | SMulAB Scalar OpAB
          | PowOpAB OpAB Integer
          | AddOpAB [OpAB]
          | MulOpAB [OpAB]
          | TProd Op Op deriving (Eq, Ord)

-- Give a rather arbitrary ordering on Cyclotomics to facilitate sorting Scalar
-- and operator terms.
instance Ord Cyclotomic where
  c <= c' = (show c) <= (show c')

instance Show Scalar where
  show (Const c) = show c
  show (Var str) = str
  show (RealVar str) = str
  show (Neg sca) = "−" ++ (showAddParen sca)
  show (Conj sca) = case sca of
    Var str -> str ++ "*"
    sca     -> "(" ++ (show sca) ++ ")*"
  show (Add scas) = intercalate " + " $ map show scas
  show (Mul scas) = intercalate "⋅" $ map showAddParen scas
  show (Abs sca) = "|" ++ (show sca) ++ "|"
  show (Sgn sca) = "sgn(" ++ (show sca) ++ ")"
  show (Pow sca n) = case sca of
    Var str -> str ++ (toSupScr n)
    sca     -> "(" ++ (show sca) ++ ")" ++ (toSupScr n)

toSupScr :: Integer -> String
toSupScr n = map repl $ show n
  where repl '-' = '⁻'
        repl '0' = '⁰'
        repl '1' = '¹'
        repl '2' = '²'
        repl '3' = '³'
        repl '4' = '⁴'
        repl '5' = '⁵'
        repl '6' = '⁶'
        repl '7' = '⁷'
        repl '8' = '⁸'
        repl '9' = '⁹'

showAddParen :: Scalar -> String
showAddParen (Add scas) = "(" ++ (intercalate " + " $ map show scas) ++ ")"
showAddParen sca = show sca

instance Num Scalar where
  (Const c1) + (Const c2) = Const $ c1 + c2
  (Add scas1) + (Add scas2) = Add (scas1 ++ scas2)
  sca + (Add scas) = Add (sca:scas)
  (Add scas) + sca = Add (scas ++ [sca])
  sca1 + sca2 = Add [sca1, sca2]
  (Sgn sca) * (Abs sca')
    | sca == sca' = sca
    | otherwise   = Mul [Sgn sca, Abs sca']
  (Const c1) * (Const c2) = Const $ c1 * c2
  (Mul scas1) * (Mul scas2) = Mul (scas1 ++ scas2)
  sca * (Mul scas) = Mul (sca:scas)
  (Mul scas) * sca = Mul (scas ++ [sca])
  sca1 * sca2 = Mul [sca1, sca2]
  negate (Neg sca) = sca
  negate (Const c) = Const $ negate c
  negate sca = Neg sca
  abs (Neg sca) = abs sca
  abs (Conj sca) = abs sca
  abs (Abs sca) = abs sca
  abs sca = Abs sca
  signum (Abs sca) = Const 1
  signum sca = Sgn sca
  fromInteger = Const . fromInteger

conjScalar :: Scalar -> Scalar
conjScalar (Const c) = Const $ conj c
conjScalar (Abs sca) = Abs sca
conjScalar (Conj sca) = sca
conjScalar (RealVar str) = RealVar str
conjScalar sca = Conj sca

instance Show Op where
  show ZeroOp = "𝟘"
  show IdOp = "𝟙"
  show (OpVar str) = str
  show (HermOpVar str) = str
  show (Dag op) = case op of
    ZeroOp  -> (show op) ++ "†"
    IdOp    -> (show op) ++ "†"
    OpVar s -> (show op) ++ "†"
    Dag op' -> (show $ Dag op') ++ "†"
    op      -> "(" ++ (show op) ++ ")†"
  show (SMul sca op) = (show sca) ++ "⋅" ++ (showAddParenOp op)
  show (PowOp op n) = case op of
    ZeroOp      -> (show op) ++ (toSupScr n)
    IdOp        -> (show op) ++ (toSupScr n)
    OpVar s     -> (show op) ++ (toSupScr n)
    HermOpVar s -> (show op) ++ (toSupScr n)
    op          -> "(" ++ (show op) ++ ")" ++ (toSupScr n)
  show (AddOp ops) = intercalate " + " $ map show ops
  show (MulOp ops) = intercalate "⋅" $ map showAddParenOp ops

showAddParenOp :: Op -> String
showAddParenOp (AddOp ops) = "(" ++ (intercalate " + " $ map show ops) ++ ")"
showAddParenOp op = show op

instance Show OpAB where
  show ZeroOpAB = "𝟘"
  show IdOpAB = "𝟙"
  show (OpABVar str) = str
  show (HermOpABVar str) = str
  show (DagAB op) = case op of
    ZeroOpAB  -> (show op) ++ "†"
    IdOpAB    -> (show op) ++ "†"
    OpABVar s -> (show op) ++ "†"
    DagAB op' -> (show $ DagAB op') ++ "†"
    op        -> "(" ++ (show op) ++ ")†"
  show (SMulAB sca op) = (show sca) ++ "⋅" ++ (showAddParenOpAB op)
  show (PowOpAB op n) = case op of
    ZeroOpAB      -> (show op) ++ (toSupScr n)
    IdOpAB        -> (show op) ++ (toSupScr n)
    OpABVar s     -> (show op) ++ (toSupScr n)
    HermOpABVar s -> (show op) ++ (toSupScr n)
    op            -> "(" ++ (show op) ++ ")" ++ (toSupScr n)
  show (AddOpAB ops) = intercalate " + " $ map show ops
  show (MulOpAB ops) = intercalate "⋅" $ map showAddParenOpAB ops
  show (TProd op1 op2) = (showAddParenOp op1) ++ "⊗" ++ (showAddParenOp op2)

showAddParenOpAB :: OpAB -> String
showAddParenOpAB (AddOpAB ops) = "(" ++ (intercalate " + " $
                                 map show ops) ++ ")"
showAddParenOpAB op = show op

infix ><
(><) :: Op -> Op -> OpAB
op1 >< op2 = TProd op1 op2

class Algebra a where
  infixr 7 /*/
  (/*/) :: a -> a -> a

  infixr 6 /+/
  (/+/) :: a -> a -> a

  dag :: a -> a

  infixr 7 */
  (*/) :: Scalar -> a -> a

instance Algebra Op where
  ZeroOp /*/ op = ZeroOp
  op /*/ ZeroOp = ZeroOp
  IdOp /*/ op = op
  op /*/ IdOp = op
  (MulOp ops1) /*/ (MulOp ops2) = MulOp (ops1 ++ ops2)
  op /*/ (MulOp ops) = MulOp (op:ops)
  (MulOp ops) /*/ op = MulOp (ops ++ [op])
  op1 /*/ op2 = MulOp [op1, op2]

  ZeroOp /+/ op = op
  op /+/ ZeroOp = op
  (AddOp ops1) /+/ (AddOp ops2) = AddOp (ops1 ++ ops2)
  op /+/ (AddOp ops) = AddOp (op:ops)
  (AddOp ops) /+/ op = AddOp (ops ++ [op])
  op1 /+/ op2 = AddOp [op1, op2]

  dag ZeroOp = ZeroOp
  dag IdOp = IdOp
  dag (HermOpVar s) = HermOpVar s
  dag (Dag op) = op
  dag op = Dag op

  (Const 0) */ op = ZeroOp
  (Const 1) */ op = op
  s */ ZeroOp = ZeroOp
  s */ (SMul s' op) = SMul (s' * s) op
  s */ op = SMul s op

instance Algebra OpAB where
  ZeroOpAB /*/ op = ZeroOpAB
  op /*/ ZeroOpAB = ZeroOpAB
  IdOpAB /*/ op = op
  op /*/ IdOpAB = op
  (TProd opa opb) /*/ (TProd opa' opb') = TProd (opa /*/ opa') (opb /*/ opb')
  (MulOpAB ops1) /*/ (MulOpAB ops2) = MulOpAB (ops1 ++ ops2)
  op /*/ (MulOpAB ops) = MulOpAB (op:ops)
  (MulOpAB ops) /*/ op = MulOpAB (ops ++ [op])
  op1 /*/ op2 = MulOpAB [op1, op2]

  ZeroOpAB /+/ op = op
  op /+/ ZeroOpAB = op
  (AddOpAB ops1) /+/ (AddOpAB ops2) = AddOpAB (ops1 ++ ops2)
  op /+/ (AddOpAB ops) = AddOpAB (op:ops)
  (AddOpAB ops) /+/ op = AddOpAB (ops ++ [op])
  op1 /+/ op2 = AddOpAB [op1, op2]

  dag ZeroOpAB = ZeroOpAB
  dag IdOpAB = IdOpAB
  dag (HermOpABVar s) = HermOpABVar s
  dag (DagAB op) = op
  dag op = DagAB op

  (Const 0) */ op = ZeroOpAB
  (Const 1) */ op = op
  s */ ZeroOpAB = ZeroOpAB
  s */ (SMulAB s' op) = SMulAB (s' * s) op
  s */ op = SMulAB s op

-- Now for some simplification algorithms

expandPow :: Scalar -> Scalar
expandPow (Neg sca) = negate $ expandPow sca
expandPow (Conj sca) = conjScalar $ expandPow sca
expandPow (Pow sca n)
  | n <= 0    = Pow sca n
  | n == 1    = sca
  | otherwise = (expandPow sca) * (expandPow $ Pow sca $ n - 1)
expandPow (Abs sca) = abs $ expandPow sca
expandPow (Sgn sca) = signum $ expandPow sca
expandPow (Add scas) = sum $ map expandPow scas
expandPow (Mul scas) = product $ map expandPow scas
expandPow sca = sca

expandPowOp :: Op -> Op
expandPowOp (Dag op) = dag $ expandPowOp op
expandPowOp (SMul sca op) = SMul sca $ expandPowOp op
expandPowOp (PowOp op n)
  | n <= 0    = PowOp op n
  | n == 1    = op
  | otherwise = (expandPowOp op) /*/ (expandPowOp $ PowOp op $ n - 1)
expandPowOp (AddOp ops) = sumOp $ map expandPowOp ops
expandPowOp (MulOp ops) = productOp $ map expandPowOp ops
expandPowOp op = op

sumOp :: Foldable t => t Op -> Op
sumOp = foldl (\acc x -> acc /+/ x) ZeroOp

productOp :: Foldable t => t Op -> Op
productOp = foldl (\acc x -> acc /*/ x) IdOp

pushDownConj :: Scalar -> Scalar
pushDownConj (Conj sca) = case sca of
  Const c     -> Const $ conj c
  Var str     -> conjScalar $ Var str
  RealVar str -> RealVar str
  Neg sca'    -> Neg $ pushDownConj $ conjScalar sca'
  Conj sca'   -> pushDownConj sca'
  Pow sca' n  -> Pow (pushDownConj $ conjScalar sca') n
  Abs sca'    -> Abs $ pushDownConj sca'
  Sgn sca'    -> Sgn $ pushDownConj $ conjScalar sca'
  Add scas    -> Add $ map (pushDownConj . conjScalar) scas
  Mul scas    -> Mul $ map (pushDownConj . conjScalar) scas
pushDownConj (Neg sca) = Neg $ pushDownConj sca
pushDownConj (Pow sca n) = Pow (pushDownConj sca) n
pushDownConj (Abs sca) = Abs $ pushDownConj sca
pushDownConj (Sgn sca) = Sgn $ pushDownConj sca
pushDownConj (Add scas) = Add $ map pushDownConj scas
pushDownConj (Mul scas) = Mul $ map pushDownConj scas
pushDownConj sca = sca

pushDownDag :: Op -> Op
pushDownDag (Dag op) = case op of
  OpVar s      -> Dag $ OpVar s
  HermOpVar s  -> HermOpVar s
  ZeroOp       -> ZeroOp
  IdOp         -> IdOp
  Dag op'      -> pushDownDag op'
  SMul s op'   -> SMul (pushDownConj $ conjScalar s) (pushDownDag $ dag op')
  PowOp op' n  -> PowOp (pushDownDag $ dag op') n
  AddOp ops    -> AddOp $ map (pushDownDag . dag) ops
  MulOp ops    -> MulOp $ map (pushDownDag . dag) $ reverse ops
pushDownDag (SMul s op) = SMul (pushDownConj s) (pushDownDag op)
pushDownDag (AddOp ops) = AddOp $ map pushDownDag ops
pushDownDag (MulOp ops) = MulOp $ map pushDownDag ops
pushDownDag op = op

pushDownDagAB :: OpAB -> OpAB
pushDownDagAB (DagAB op) = case op of
  OpABVar s     -> DagAB $ OpABVar s
  HermOpABVar s -> HermOpABVar s
  ZeroOpAB      -> ZeroOpAB
  IdOpAB        -> IdOpAB
  DagAB op'     -> pushDownDagAB op'
  SMulAB s op'  -> SMulAB (pushDownConj $ conjScalar s)
                   (pushDownDagAB $ dag op')
  PowOpAB op' n -> PowOpAB (pushDownDagAB $ dag op') n
  AddOpAB ops   -> AddOpAB $ map (pushDownDagAB . dag) ops
  MulOpAB ops   -> MulOpAB $ map (pushDownDagAB . dag) $ reverse ops
  TProd op1 op2 -> TProd (pushDownDag $ dag op1) (pushDownDag $ dag op2)
pushDownDagAB (SMulAB s op) = SMulAB (pushDownConj s) (pushDownDagAB op)
pushDownDagAB (AddOpAB ops) = AddOpAB $ map pushDownDagAB ops
pushDownDagAB (MulOpAB ops) = MulOpAB $ map pushDownDagAB ops
pushDownDagAB (TProd op1 op2) = TProd (pushDownDag op1) (pushDownDag op2)
pushDownDagAB op = op

bindScalars :: Op -> Op
bindScalars (SMul sca op) = case op of
  MulOp []       -> SMul sca IdOp
  MulOp (op:ops) -> MulOp $ map bindScalars $ (SMul sca op):ops
  AddOp []       -> ZeroOp
  AddOp ops      -> AddOp $ map (bindScalars . (SMul sca)) ops
  ZeroOp         -> ZeroOp
  op             -> SMul sca op
bindScalars (Dag op) = dag $ bindScalars op
bindScalars (PowOp op n) = PowOp (bindScalars op) n
bindScalars (AddOp ops) = sumOp $ map bindScalars ops
bindScalars (MulOp ops) = productOp $ map bindScalars ops
bindScalars op = op

-- This function is designed to be called after pushDownDag and bindScalars
listDistribute :: Op -> [(Scalar, [Op])]
listDistribute ZeroOp = []
listDistribute IdOp = [(Const 1, [])]
listDistribute (SMul sca op) = [(sca, [op])]
listDistribute (AddOp ops) = concat $ map listDistribute ops
listDistribute (MulOp ops) = map combProdList $ sequence $ map listDistribute ops
  where combProdList = foldr (\(s, ops) (s', ops') -> (s * s', ops ++ ops'))
                       (Const 1, [])
listDistribute op = [(Const 1, [op])]

expandOp :: Op -> Op
expandOp = sumOp . (map (\(sca, ops) -> SMul sca $ productOp ops)) .
           listDistribute . bindScalars . pushDownDag
