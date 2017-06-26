{-# LANGUAGE ExistentialQuantification #-}
import Data.List
{-
data Expr a = Const a
            | Var String
            | Fn String [Expr b]
-}
-- The above won't compile, because 'b' isn't in scope. I would love to create
-- an abstract type that could have constants, variables, and abstract functions
-- from an arbitrary type to this type. My difficulty seems to be in
-- representing these abstract functions.

-- Not sure if there's a point to have the function [b] -> a included in the Fn
-- constructor. I include it now with the idea of enforcing the correct type of
-- expressions in the list, but this might be effected in a better way.
data Expr a = Const a
            | Var String
            | forall b. Show b => Fn String ([b] -> a) [Expr b]

instance (Show a) => Show (Expr a) where
  show (Const a) = show a
  show (Fn str _ []) = str
  show (Fn "sum" _ exps) = "(" ++ (intercalate "+" $ map show exps) ++ ")"
  show (Fn "product" _ exps) = "(" ++ (intercalate "*" $ map show exps) ++ ")"
  show (Fn str _ exps) = str ++ "(" ++ (intercalate "," $ map show exps) ++ ")"

-- The stuff above kind of works now, using forall to get b in the picture. The
-- stuff below has the difficulty that I am not currently forcing the arguments
-- of my functions to be of type a (they are generally of type b), so I can't
-- make a list of b out of them.
{-
instance (Num a, Show a) => Num (Expr a) where
  Const x + Const y = Const $ x + y
  (Fn "sum" fn xs) + (Fn "sum" _ ys) = Fn "sum" fn (xs ++ ys)
  (Fn "sum" fn xs) + y = Fn "sum" fn (xs ++ [y])
  x + (Fn "sum" fn ys) = Fn "sum" fn (x:ys)
  x + y = Fn "sum" sum [x, y]
  Const x * Const y = Const $ x * y
  (Fn "product" fn xs) * (Fn "product" _ ys) = Fn "product" fn (xs ++ ys)
  (Fn "product" fn xs) * y = Fn "product" fn (xs ++ [y])
  x * (Fn "product" fn ys) = Fn "product" fn (x:ys)
  x * y = Fn "product" product [x, y]
  abs (Const x) = Const $ abs x
  abs (Fn "negate" _ (x:[])) = Fn "abs" (abs . head) [x]
  abs x = Fn "abs" (abs . head) [x]
  signum (Const x) = Const $ (signum . head) x
  signum x = Fn "sigmnum" (signum . head) [x]
  fromInteger n = Const $ fromInteger n
  negate (Const x) = Const $ negate x
  negate (Fn "negate" _ (x:[])) = x
  negate x = Fn "negate" (negate . head) [x]
-}
