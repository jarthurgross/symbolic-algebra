import Data.List

data Expr a = Const a | Var Char Type | Fn String [Expr a]

data Type = Scalar | Vector | Operator

infixshow :: (Show a) => String -> [Expr a] -> String
infixshow s xs = "(" ++ (intercalate s $ map show xs) ++ ")"

instance (Show a) => Show (Expr a) where
  show (Const a) = show a
  show (Var x Scalar) = [x]
  show (Var x Vector) = [x] ++ "\8401" -- Put an arrow over vectors
  show (Var x Operator) = [x] ++ "\770" -- Put a hat on operators
  show (Fn "add" xs) = infixshow "+" xs
  show (Fn "tprod" xs) = infixshow "⊗" xs
  show (Fn s xs) = s ++ "(" ++ (intercalate "," $ map show xs) ++ ")"

sin' :: Expr a -> Expr a
sin' = (Fn "sin") . (flip (:)) []

max' :: Expr a -> Expr a -> Expr a
max' x y = Fn "max" [x, y]

add' :: [Expr a] -> Expr a
add' = Fn "add"

tprod :: [Expr a] -> Expr a
tprod = Fn "tprod"

infixmathml :: (Show a) => String -> [Expr a] -> String
infixmathml s xs = "<mfenced><mrow>" ++ (intercalate ("<mo>" ++ s ++ "</mo>") $ map mathml xs) ++ "</mrow></mfenced>"

mathml :: (Show a) => Expr a -> String
mathml (Const c) = "<mn>" ++ (show c) ++ "</mn>"
mathml (Var x Scalar) = "<mi>" ++ [x] ++ "</mi>"
mathml (Var x Vector) = "<mi mathvariant='bold'>" ++ [x] ++ "</mi>"
mathml (Var x Operator) = "<mover><mi>" ++ [x] ++ "</mi><mo>^</mo></mover>"
mathml (Fn "add" xs) = infixmathml "+" xs
mathml (Fn "tprod" xs) = infixmathml "&#x2297;" xs
mathml (Fn s xs) = "<mi>" ++ s ++ "</mi>" ++ "<mfenced>" ++ concat (map mathml xs) ++ "</mfenced>"

showmathml :: (Show a) => Expr a -> String
showmathml e = "<math>" ++ (mathml e) ++ "</math>"
