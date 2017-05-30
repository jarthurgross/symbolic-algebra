import Data.List
import qualified Data.Map as Map
import qualified Data.List.Ordered as Ordered

p = Atom "p"
q = Atom "q"
r = Atom "r"

t = Const True
f = Const False

data TruthTable = TruthTable { tableAtoms :: [Prop]
                             , tableProps :: [Prop]
                             , valuations :: [([Bool], [Bool])]
                             }

data Prop = Const Bool
          | Atom String
          | Not Prop
          | And Prop Prop
          | Or Prop Prop
          | Imp Prop Prop
          | Iff Prop Prop deriving (Eq, Ord)

instance Show Prop where
  show (Const True) = "⊤"
  show (Const False) = "⊥"
  show (Atom s) = s
  show (Not p) = "¬" ++ (show p)
  show (And p1 p2) = "(" ++ (show p1) ++ " ∧ " ++ (show p2) ++ ")"
  show (Or p1 p2) = "(" ++ (show p1) ++ " ∨ " ++ (show p2) ++ ")"
  show (Imp p1 p2) = "(" ++ (show p1) ++ " → " ++ (show p2) ++ ")"
  show (Iff p1 p2) = "(" ++ (show p1) ++ " ↔ " ++ (show p2) ++ ")"

instance Num Prop where
  (Const True) * p = p
  p * (Const True) = p
  (Const False) * p = Const False
  p * (Const False) = Const False
  p1 * p2 = And p1 p2
  (Const True) + p = Const True
  p + (Const True) = Const True
  (Const False) + p = p
  p + (Const False) = p
  p1 + p2 = Or p1 p2
  abs p = Const True
  signum p = p
  -- fromInteger is included for completeness, but it doesn't make a whole lot
  -- of sense (i.e. fromInteger (1 * 1) == (fromInteger 1) * (fromInteger 1),
  -- but fromInteger (1 - 1) /= (fromInteger 1) - (fromInteger 1))
  fromInteger n
    | n `mod` 2 == 0 = Const False
    | otherwise      = Const True
  negate p = Not p

infixr 5 ==>
(==>) :: Prop -> Prop -> Prop
p ==> q = Imp p q

infixr 5 <=>
(<=>) :: Prop -> Prop -> Prop
p <=> q = Iff p q

infix 4 |=>
(|=>) :: Prop -> Prop -> (Prop -> Prop)
(Atom s) |=> p = subs (Atom s) p
_ |=> _ = error "Cannot substitute for non-atom"

-- This could be improved by spacing the valuations of propositions according
-- to the length of each proposition's representation, but it gets the job done.
instance Show TruthTable where
  show tt = intercalate "\n" $ header:divLine:rows
    where atomHeader = intercalate "│" $ map show $ tableAtoms tt
          propHeader = spaceSep $ map show $ tableProps tt
          header = atomHeader ++ " ║ " ++ propHeader
          divLine = atomBar ++ "═╬═" ++ (makeBar propHeader)
          atomBar = intercalate "╪" $ replicate (length $ tableAtoms tt) "═"
          makeBar s = replicate (length s) '═'
          rowFn val = (intercalate "│" $ map boolShow $ fst val) ++ " ║ " ++
                      (spaceSep $ map boolShow $ snd val)
          rows = map rowFn $ valuations tt
          boolShow True = "⊤" 
          boolShow False = "⊥"
          spaceSep = intercalate " "

-- Could try refining this to output [Atom]. Also, this outputs the Atoms sorted
-- (which is important for dependent functions, such as building a Map from an
-- AscList with Atoms as keys.).
atoms :: Prop -> [Prop]
atoms (Const True) = []
atoms (Const False) = []
atoms (Atom s) = [Atom s]
atoms (Not p) = atoms p
atoms (And p q) = Ordered.union (atoms p) (atoms q)
atoms (Or p q) = Ordered.union (atoms p) (atoms q)
atoms (Imp p q) = Ordered.union (atoms p) (atoms q)
atoms (Iff p q) = Ordered.union (atoms p) (atoms q)

-- Might also refine the second argument to be from Atom -> Bool
eval :: Prop -> (Prop -> Bool) -> Bool
eval (Const True) _ = True
eval (Const False) _ = False
eval (Atom s) v = v (Atom s)
eval (Not p) v = not $ eval p v
eval (And p q) v = (eval p v) && (eval q v)
eval (Or p q) v = (eval p v) || (eval q v)
eval (Imp p q) v = (not $ eval p v) || (eval q v)
eval (Iff p q) v = (eval p v) == (eval q v)

truthTable :: [Prop] -> TruthTable
truthTable ps = TruthTable { tableAtoms = as
                           , tableProps = ps
                           , valuations = vals
                           }
  where as = foldl union [] $ map atoms ps
        aVs = allValuations as
        vals = [(aV, map (flip eval $ valsToFn aV) ps) | aV <- aVs]
        valsToFn = atomValsToFn . Map.fromAscList . zip as

tautology :: Prop -> Bool
tautology p = and $ (map (flip eval) vs) <*> [p]
  where vs = atomValsToFn <$> Map.fromAscList <$> (zip as) <$> allValuations as
        as = atoms p

unsatisfiable :: Prop -> Bool
unsatisfiable = tautology . Not

satisfiable :: Prop -> Bool
satisfiable = not . unsatisfiable

allValuations :: [Prop] -> [[Bool]]
allValuations as = sequence $ replicate (length as) [False, True]

atomValsToFn :: Map.Map Prop Bool -> (Prop -> Bool)
atomValsToFn = flip (Map.findWithDefault False)

-- Should refine the first argument to be an Atom
subs :: Prop -> Prop -> Prop -> Prop
subs _ _ (Const True) = Const True
subs _ _ (Const False) = Const False
subs (Atom s) asub (Atom s') = if s == s' then asub else (Atom s')
subs a asub (Not p) = Not $ subs a asub p
subs a asub (And p q) = And (subs a asub p) (subs a asub q)
subs a asub (Or p q) = Or (subs a asub p) (subs a asub q)
subs a asub (Imp p q) = Imp (subs a asub p) (subs a asub q)
subs a asub (Iff p q) = Iff (subs a asub p) (subs a asub q)
subs _ _ _ = error "Cannot substitute for non-atom"
