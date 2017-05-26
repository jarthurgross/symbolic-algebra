import Data.List
import Data.Ratio
import qualified Data.Map as Map

expr = Sum [A
           , Id
           , Dagger A
           , Dagger Id
           , Dagger (Sum [A
                         , Dagger A
                         , Id
                         , Prod [A, Id, Dagger A, A]])
           , Prod [Dagger A, A, A]]

data Expr = A
          | Id
          | Dagger Expr
          | Sum [Expr]
          | Prod [Expr]
          | SMul Rational Expr deriving (Eq, Ord)

instance Show Expr where
  show A = "a"
  show Id = "𝟙"
  show (Dagger e) = case e of
    A  -> (show A) ++ "†"
    Id -> show Id
    e  -> "(" ++ (show e) ++ ")†"
  show (Sum es) = "(" ++ (intercalate "+" $ map show es) ++ ")"
  show (Prod es) = concat $ map show es
  show (SMul r e) = (showRat r) ++ (show e)

showRat :: Rational -> String
showRat r
  | d == 1    = show n
  | otherwise = (show n) ++ "/" ++ (show d)
  where d = denominator r
        n = numerator r

distDag :: Expr -> Expr
distDag (Dagger Id) = Id
distDag (Dagger (Dagger e)) = distDag e
distDag (Dagger (Sum es)) = Sum $ map (distDag . Dagger) es
distDag (Dagger (Prod es)) = Prod $ map (distDag . Dagger) $ reverse es
distDag (Dagger (SMul r e)) = SMul r $ distDag $ Dagger e
distDag (Sum es) = Sum $ map distDag es
distDag (Prod es) = Prod $ map distDag es
distDag (SMul r e) = SMul r $ distDag e
distDag e = e

expand :: Expr -> Expr
expand = Sum . (map formProd) . listSimplify
  where formProd (e:[], 1) = e
        formProd (e:[], r) = SMul r e
        formProd (es, 1)   = Prod es
        formProd (es, r)   = SMul r $ Prod es

listSimplify = collect . (map applyId) . listExpand . distDag

-- The Expr in the output of listExpand should be a restricted Expr that has no
-- Sum, Prod, or SMul, and Daggers drilled down to As. The Expr passed shoud
-- have Daggers drilled down to As.
listExpand :: Expr -> [([Expr], Rational)]
listExpand (Sum es) = concat $ map listExpand es
listExpand (Prod es) = map combineProds cartProd
  where cartProd = sequence $ map listExpand es
        combineProds = foldr (\(es, r) (esa, ra) -> (es ++ esa, r * ra)) ([], 1)
listExpand (SMul r e) = map (\(e, r') -> (e, r * r')) $ listExpand e
listExpand e = [([e], 1)]

-- Take a non-empty list of Expr (restricted to A, Dagger A, and Id)
-- representing a product and remove the Ids (unless it is the singleton list
-- [Id]).
applyId :: ([Expr], Rational) -> ([Expr], Rational)
applyId ([Id], r) = ([Id], r)
applyId (es, r) = (filter (/= Id) es, r)

-- This combines terms with equal [Expr] products bu multiplying the scalars.
collect :: [([Expr], Rational)] -> [([Expr], Rational)]
collect = Map.toList . Map.fromListWith (+)

normalOrder :: Expr -> Expr
normalOrder = (converge (==) . (iterate $ expand . commuteAs)) . expand

commuteAs :: Expr -> Expr
commuteAs (Dagger e) = Dagger (commuteAs e)
commuteAs (Sum es) = Sum $ map commuteAs es
commuteAs (Prod es) = Prod $ listCommute $ map commuteAs es
commuteAs (SMul r es) = SMul r $ commuteAs es
commuteAs e = e

listCommute :: [Expr] -> [Expr]
listCommute (A:(Dagger A):es) = (Sum [Prod [Dagger A, A], Id]):es
listCommute (e:es) = e:(listCommute es)
listCommute [] = []

-- Applies a function repeatedly until the last two function applications
-- satisfy some convergence criterion, returning the last function application.
-- Taken from http://stackoverflow.com/a/7443379/1236650
converge :: (a -> a -> Bool) -> [a] -> a
converge p (x:ys@(y:_))
  | p x y     = y
  | otherwise = converge p ys
