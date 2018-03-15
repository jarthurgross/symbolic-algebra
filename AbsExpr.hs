{-# LANGUAGE ExistentialQuantification #-}
import Data.List

data Expr a = Const a
            | Var String
            | forall b. AppFn (Fn a b) (Expr b)

data Fn a b = Fn String

instance Show a => Show (Expr a) where
  show (Const a) = show a
  show (Var str) = str
  show (AppFn fn expr) = (show fn) ++ "(" ++
                         (intercalate "," $ map show

instance Show Fn where
  show (Fn str) = str
