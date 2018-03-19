-- Constant datatype including radicals and the imaginary unit

import Data.List
import Data.Ratio
import GHC.Real

data Constant = CInt Integer
              | Sqrt Integer
              | CNeg Constant
              | CRat Constant Constant
              | CI
              | CSum [Constant]
              | CProd [Constant] deriving (Eq, Ord)

instance Show Constant where
  show (CInt n) = show n
  show (Sqrt n) = "√\773" ++ (intersperse '\773' (show n))
  show (CNeg const) = "−" ++ (showConstAddParen const)
  show (CRat const1 const2) = (show const1) ++ "/" ++ (show const2)
  show CI = "i"
  show (CSum (const1:(CNeg const2):consts)) = (show const1) ++ "−" ++
                                              (show $ CSum $ const2:consts)
  show (CSum (const1:const2:consts)) = (show const1) ++ "+" ++
                                       (show $ CSum $ const2:consts)
  show (CSum (const:_)) = show const
  show (CProd consts) = intercalate "⋅" $ map showConstAddParen consts

showConstAddParen :: Constant -> String
showConstAddParen (CSum consts) = "(" ++ (intercalate "+" $
                                          map show consts) ++ ")"
showConstAddParen const = show const

instance Num Constant where
  (CInt n) + (CInt m) = CInt $ n + m
  (CSum consts1) + (CSum consts2) = CSum $ consts1 ++ consts2
  const + (CSum consts) = CSum $ const:consts
  (CSum consts) + const = CSum $ consts ++ [const]
  const1 + const2 = CSum [const1, const2]
  (CInt n) * (CInt m) = CInt $ m * n
  (CRat num1 denom1) * (CRat num2 denom2) = CRat (num1 * num2) (denom1 * denom2)
  const * (CRat num denom) = CRat (const * num) denom
  (CRat num denom) * const = CRat (num * const) denom
  (CProd consts1) * (CProd consts2) = CProd $ consts1 ++ consts2
  const * (CProd consts) = CProd $ const:consts
  (CProd consts) * const = CProd $ consts ++ [const]
  const1 * const2 = CProd [const1, const2]
  negate (CNeg const) = const
  negate const = CNeg const
  abs const = const -- Dummy implementation
  signum const = 1 -- Dummy implementation
  fromInteger = CInt

instance Fractional Constant where
  fromRational (p :% q) = CRat (CInt p) (CInt q)
  recip (CRat num denom) = CRat denom num
  recip const = CRat (CInt 1) const

conjConst :: Constant -> Constant
conjConst (CInt n) = CInt n
conjConst (Sqrt n) = Sqrt n
conjConst CI = CNeg CI
conjConst const = travConstConst conjConst const

travConstConst :: (Constant -> Constant) -> Constant -> Constant
travConstConst fnConst (CNeg const) = CNeg $ fnConst const
travConstConst fnConst (CRat const1 const2) = CRat (fnConst const1)
                                              (fnConst const2)
travConstConst fnConst (CSum consts) = CSum $ map fnConst consts
travConstConst fnConst (CProd consts) = CProd $ map fnConst consts
travConstConst _ const = const
