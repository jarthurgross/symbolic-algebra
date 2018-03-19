-- Constant datatype including radicals and the imaginary unit

module Constant where

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
  (CInt 0) + const = const
  const + (CInt 0) = const
  (CInt n) + (CInt m) = CInt $ n + m
  (CSum consts1) + (CSum consts2) = CSum $ consts1 ++ consts2
  const + (CSum consts) = CSum $ const:consts
  (CSum consts) + const = CSum $ consts ++ [const]
  const1 + const2 = CSum [const1, const2]

  CI * CI = negate 1
  (CInt 0) * const = CInt 0
  const * (CInt 0) = CInt 0
  (CInt 1) * const = const
  const * (CInt 1) = const
  (CInt (-1)) * const = negate const
  const * (CInt (-1)) = negate const
  (CInt n) * (CInt m) = CInt $ m * n
  (CRat num1 denom1) * (CRat num2 denom2) = CRat (num1 * num2) (denom1 * denom2)
  const * (CRat num denom) = CRat (const * num) denom
  (CRat num denom) * const = CRat (num * const) denom
  (CProd consts1) * (CProd consts2) = CProd $ consts1 ++ consts2
  const * (CProd consts) = CProd $ const:consts
  (CProd consts) * const = CProd $ consts ++ [const]
  -- By including rules for multiplying negated constants, we can bubble the
  -- negations up to the top level of a product when putting things in canonical
  -- form (e.g., distributeConst).
  (CNeg const1) * (CNeg const2) = const1 * const2
  (CNeg const1) * const2 = negate $ const1 * const2
  const1 * (CNeg const2) = negate $ const1 * const2
  const1 * const2 = CProd [const1, const2]
  negate (CNeg const) = const
  negate const = CNeg const
  abs const = const -- Dummy implementation
  signum const = 1 -- Dummy implementation
  fromInteger n
    | n >= 0    = CInt n
    | otherwise = CNeg $ CInt $ negate n

instance Fractional Constant where
  fromRational (p :% q) = CRat (fromInteger p) (fromInteger q)
  recip (CRat num denom) = CRat denom num
  recip const = CRat (CInt 1) const

conjConst :: Constant -> Constant
conjConst (CInt n) = CInt n
conjConst (Sqrt n) = Sqrt n
conjConst CI = CNeg CI
conjConst const = travConstConst conjConst const

pushDownNegConst :: Constant -> Constant
pushDownNegConst (CNeg (CNeg const)) = pushDownNegConst const
pushDownNegConst (CNeg (CRat num denom)) = CRat
                                           (pushDownNegConst $ negate num) denom
pushDownNegConst (CNeg (CSum consts)) = CSum $
                                        map (pushDownNegConst . negate) consts
pushDownNegConst (CNeg (CProd (const:consts))) = CProd $ (pushDownNegConst $
                                                 negate const):consts
pushDownNegConst const = travConstConst pushDownNegConst const

listDistributeConst :: Constant -> [[Constant]]
listDistributeConst (CInt 0) = []
listDistributeConst (CSum consts) = concat $ map listDistributeConst consts
listDistributeConst (CProd consts) = foldr (\consts1 consts2 ->
                                            (++) <$> consts1 <*> consts2)
                                     [[]] $ map listDistributeConst consts
listDistributeConst const = [[const]]

distributeConst :: Constant -> Constant
distributeConst = sum . (map product) . listDistributeConst . pushDownNegConst

travConstConst :: (Constant -> Constant) -> Constant -> Constant
travConstConst fnConst (CNeg const) = CNeg $ fnConst const
travConstConst fnConst (CRat const1 const2) = CRat (fnConst const1)
                                              (fnConst const2)
travConstConst fnConst (CSum consts) = CSum $ map fnConst consts
travConstConst fnConst (CProd consts) = CProd $ map fnConst consts
travConstConst _ const = const
