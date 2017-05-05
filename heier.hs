import Data.Maybe
import Data.Monoid
import Data.Group

data MyGrp = Id | Atom Char | Prdct MyGrp MyGrp | Inv MyGrp deriving (Eq)

instance Monoid MyGrp where
  mempty = Id
  mappend Id a = a
  mappend a Id = a
  mappend a (Inv b) = case a == b of
    True -> Id
    False -> Prdct a (Inv b)
  mappend (Inv a) b = case a == b of
    True -> Id
    False -> Prdct (Inv a) b
  mappend a b = Prdct a b

instance Group MyGrp where
  invert (Inv a) = a
  invert a = Inv a
--  pow a n = case compare n 0 of
--    LT -> pow (invert a) $ negate n
--    EQ -> mempty
--    GT -> mappend a (pow a (n - 1))

instance Show MyGrp where
  show Id = "1"
  show (Atom a) = [a]
  show (Inv a) = show a ++ "⁻¹"
  show (Prdct a b) = (show a) ++ (show b)

data MyField = Const Integer | FAtom Char | AInv MyField | MInv MyField | FPrdct MyField MyField | Sm [MyField] deriving (Eq)

class Group a => Field a where
  rplus :: a -> a -> a
  rplus = mappend

  rprod :: (Integral n) => a -> n -> a
  rprod = pow

  rnegate :: a -> a
  rnegate = invert

  rzero :: a
  rzero = mempty

  rmult :: a -> a -> a
  rinverse :: a -> Maybe a
  runit :: a

instance Monoid MyField where
  mempty = Const 0
  mappend (Const 0) a = a
  mappend a (Const 0) = a
  mappend a (AInv b) = case a == b of
    True -> Const 0
    False -> Sm [a, AInv b]
  mappend (AInv a) b = case a == b of
    True -> Const 0
    False -> Sm [AInv a, b]
  mappend (Const n) (Const m) = Const (n + m)
  mappend a b = Sm [a, b]

instance Group MyField where
  invert (AInv a) = a
  invert a = AInv a
  pow a n = case compare n 0 of
    LT -> pow (invert a) $ negate n
    EQ -> mempty
    GT -> mappend a (pow a (n - 1))

instance Field MyField where
  runit = Const 1
  rinverse (Const 0) = Nothing
  rinverse (MInv a) = Just a
  rinverse a = Just (MInv a)
  rmult a (Const 1) = a
  rmult (Const 1) a = a
  rmult a (MInv b) = case a == b of
    True -> Const 1
    False -> FPrdct a (MInv b)
  rmult (MInv a) b = case a == b of
    True -> Const 1
    False -> FPrdct (MInv a) b
  rmult a b = FPrdct a b

instance Show MyField where
  show (Const n) = show n
  show (FAtom a) = [a]
  show (AInv a) = "−" ++ show a
  show (MInv a) = show a ++ "⁻¹"
  show (FPrdct a b) = (show a) ++ (show b)
  show (Sm as) = "(" ++ showSum as ++ ")"
    where showSum (a:(AInv b):[]) = (show a) ++ "−" ++ (show b)
          showSum (a:(AInv b):c:ds) = (show a) ++ "−" ++ (showSum (b:c:ds))
          showSum (a:b:[]) = (show a) ++ "+" ++ (show b)
          showSum (a:b:cs) = (show a) ++ "+" ++ (showSum (b:cs))

instance Num MyField where
  (+) = rplus
  (*) = rmult
  abs = id
  negate = rnegate
  signum _ = runit
  fromInteger n = Const n

-- It would be nice if there were a way to emply 'join' to do this for us, and
-- if we could define things in such a way that I could define it for the
-- 'field' typeclass instead of only 'MyField'. I suspect I may need to define
-- new typeclasses 'AbstractGroup', etc., in order to really do what I want.
flattenSum :: MyField -> MyField
flattenSum (Sm as) = Sm (breakSums as)
  where breakSums ((Sm as):bs) = as ++ (breakSums bs)
        breakSums (a:bs) = a:(breakSums bs)
        breakSums [] = []
flattenSum a = a
