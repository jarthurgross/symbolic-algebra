data Expr a = Const a
            | Var String
            | Fn String [Expr b]
-- The above won't compile, because 'b' isn't in scope. I would love to create
-- an abstract type that could have constants, variables, and abstract functions
-- from an arbitrary type to this type. My difficulty seems to be in
-- representing these abstract functions.

data Op = Id

trace :: Expr Op -> Expr Rational
trace op = Fn "trace" [op]
