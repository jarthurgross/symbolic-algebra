import Data.List
import qualified Data.Map as Map

p = Atom "p"
q = Atom "q"

data Table = Table [String]

data Prop = T
          | F
          | Atom String
          | Not Prop
          | And Prop Prop
          | Or Prop Prop
          | Imp Prop Prop
          | Iff Prop Prop deriving (Eq, Ord)

instance Show Prop where
  show T = "⊤"
  show F = "⊥"
  show (Atom s) = s
  show (Not p) = "¬" ++ (show p)
  show (And p1 p2) = "(" ++ (show p1) ++ " ∧ " ++ (show p2) ++ ")"
  show (Or p1 p2) = "(" ++ (show p1) ++ " ∨ " ++ (show p2) ++ ")"
  show (Imp p1 p2) = "(" ++ (show p1) ++ " → " ++ (show p2) ++ ")"
  show (Iff p1 p2) = "(" ++ (show p1) ++ " ↔ " ++ (show p2) ++ ")"

instance Num Prop where
  T * p = p
  p * T = p
  F * p = F
  p * F = p
  p1 * p2 = And p1 p2
  T + p = T
  p + T = T
  F + p = p
  p + F = p
  p1 + p2 = Or p1 p2
  abs p = T
  signum p = p
  fromInteger n
    | n `mod` 2 == 0 = F
    | otherwise    = T
  negate p = Not p

instance Show Table where
  show (Table rows) = intercalate "\n" rows

-- Could try refining this to output [Atom]
atoms :: Prop -> [Prop]
atoms T = []
atoms F = []
atoms (Atom s) = [Atom s]
atoms (Not p) = atoms p
atoms (And p q) = union (atoms p) (atoms q)
atoms (Or p q) = union (atoms p) (atoms q)
atoms (Imp p q) = union (atoms p) (atoms q)
atoms (Iff p q) = union (atoms p) (atoms q)

-- Might also refine the second argument to be from Atom -> Bool
eval :: Prop -> (Prop -> Bool) -> Bool
eval T _ = True
eval F _ = False
eval (Atom s) v = v (Atom s)
eval (Not p) v = not $ eval p v
eval (And p q) v = (eval p v) && (eval q v)
eval (Or p q) v = (eval p v) || (eval q v)
eval (Imp p q) v = (not $ eval p v) || (eval q v)
eval (Iff p q) v = (eval p v) == (eval q v)

(==>) :: Prop -> Prop -> Prop
p ==> q = Imp p q

(<=>) :: Prop -> Prop -> Prop
p <=> q = Iff p q

-- This truth-table code is pretty hackish right now, but it works.

valFromLists :: [Prop] -> [Bool] -> Prop -> Bool
valFromLists as bs =  flip (Map.findWithDefault False) $ Map.fromAscList kvs
  where kvs = zip as bs

truthTable :: Prop -> [[Bool]]
truthTable p = [valList ++ [eval p $ valFromLists as valList]
               | valList <- valLists]
  where valLists = sequence $ replicate (length as) [False, True]
        as = atoms p

showTruthTable :: Prop -> Table
showTruthTable p = Table $ [header, (replicate (length header) '―')] ++ values
  where header = intercalate " " $ (map (\(Atom s) -> s) $ atoms p) ++ [show p]
        values = map (intercalate " " . (map (\b -> if b then "⊤" else "⊥"))) $
                 truthTable p

