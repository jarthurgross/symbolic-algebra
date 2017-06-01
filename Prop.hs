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
  -- fromInteger doesn't make a whole lot of sense for some applications
  -- (i.e. fromInteger (1 * 1) == (fromInteger 1) * (fromInteger 1), but
  -- fromInteger (1 - 1) /= (fromInteger 1) - (fromInteger 1)), but it is
  -- important to define it this way so that sum and product work as expected,
  -- since Const False is the additive (Or) identity, and Const True is the
  -- multiplicitive (And) identity.
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

elimConsts :: Prop -> Prop
elimConsts (Const b) = Const b
elimConsts (Atom s) = Atom s
elimConsts (Not (Const b)) = Const $ not b
elimConsts (Not p) = elimConsts' $ Not $ elimConsts p
elimConsts (And (Const False) p) = Const False
elimConsts (And p (Const False)) = Const False
elimConsts (And (Const True) p) = elimConsts p
elimConsts (And p (Const True)) = elimConsts p
elimConsts (And p q) = elimConsts' $ And (elimConsts p) (elimConsts q)
elimConsts (Or p (Const True)) = Const True
elimConsts (Or (Const True) p) = Const True
elimConsts (Or p (Const False)) = p
elimConsts (Or (Const False) p) = p
elimConsts (Or p q) = elimConsts' $ Or (elimConsts p) (elimConsts q)
elimConsts (Imp (Const True) p) = elimConsts p
elimConsts (Imp (Const False) p) = Const True
elimConsts (Imp p (Const True)) = Const True
elimConsts (Imp p (Const False)) = elimConsts $ Not p
elimConsts (Imp p q) = elimConsts' $ Imp (elimConsts p) (elimConsts q)
elimConsts (Iff (Const True) p) = elimConsts p
elimConsts (Iff p (Const True)) = elimConsts p
elimConsts (Iff (Const False) p) = elimConsts' $ Not $ elimConsts p
elimConsts (Iff p (Const False)) = elimConsts' $ Not $ elimConsts p
elimConsts (Iff p q) = elimConsts' $ Iff (elimConsts p) (elimConsts q)

-- This function assumes sub-expressions in binary operators have already had
-- constants eliminated (or are in fact simply constants)
elimConsts' :: Prop -> Prop
elimConsts' (Not (Const b)) = Const $ not b
elimConsts' (And (Const False) p) = Const False
elimConsts' (And p (Const False)) = Const False
elimConsts' (And (Const True) p) = p
elimConsts' (And p (Const True)) = p
elimConsts' (Or p (Const True)) = Const True
elimConsts' (Or (Const True) p) = Const True
elimConsts' (Or p (Const False)) = p
elimConsts' (Or (Const False) p) = p
elimConsts' (Imp p (Const True)) = Const True
elimConsts' (Imp p (Const False)) = elimConsts' $ Not p
elimConsts' (Imp (Const True) p) = p
elimConsts' (Imp (Const False) p) = Const True
elimConsts' (Iff (Const False) p) = elimConsts' $ Not p
elimConsts' (Iff p (Const False)) = elimConsts' $ Not p
elimConsts' (Iff (Const True) p) = p
elimConsts' (Iff p (Const True)) = p
elimConsts' p = p

nnf = nnf' . elimConsts

-- Assumes all constants have been eliminated, or else the proposition is only
-- a constant (maybe this could be expressed using refinement types?)
nnf' :: Prop -> Prop
nnf' (Not (Not p)) = nnf' p
nnf' (Not (And p q)) = nnf' $ Or (Not p) (Not q)
nnf' (Not (Or p q)) = nnf' $ And (Not p) (Not q)
nnf' (Not (Imp p q)) = nnf' $ And p (Not q)
nnf' (Not (Iff p q)) = Or (nnf' $ And p (Not q)) (nnf' $ And (Not p) q)
nnf' (And p q) = And (nnf' p) (nnf' q)
nnf' (Or p q) = Or (nnf' p) (nnf' q)
nnf' (Imp p q) = Or (nnf' $ Not p) (nnf' q)
nnf' (Iff p q) = Or (nnf' $ And p q) (nnf' $ And (Not p) (Not q))
nnf' p = p

-- Put an expression in disjunctive normal form using its truth table
ttdnf :: Prop -> Prop
ttdnf p = sum $ map product disjuncts
  where tt = truthTable [p]
        as = tableAtoms tt
        pVals = map (head . snd) $ valuations tt
        atomValPairs = map (zip as) satAtomVals
        satAtomVals = map fst $ filter ((== True) . head . snd) $ valuations tt
        disjuncts = map (map (\(a, b) -> if b then a else Not a)) atomValPairs

-- Put an expression in conjunctive normal form using its truth table
ttcnf :: Prop -> Prop
ttcnf = nnf' . Not . ttdnf . Not

dnf :: Prop -> Prop
dnf = sum . (map product) . (filter noContradictions) . disjunctList . nnf

noContradictions :: [Prop] -> Bool
noContradictions ps = [] == Ordered.isect pos neg
  where (pos, neg) = foldr sortPosNeg ([], []) ps
        sortPosNeg (Not (Atom s)) acc = (fst acc, (Atom s):(snd acc))
        sortPosNeg (Atom s) acc = ((Atom s):(fst acc), snd acc)

-- The next optimization waiting to be done is detecting when a sub disjunct
-- is being added to the list and eliminating all super disjuncts at that time.
-- Making this efficient seems like it will involve understanding how
-- Ordered.insertSet works, and might be helped by providing an explicit
-- ordering on ordered lists of Props.
-- Currently we remove super disjuncts at each joining step. Not sure if that's
-- the most efficient or not, but at least it appears to work for us.
disjunctList :: Prop -> [[Prop]]
-- ordCartProd looks arcane, but it is meant to do a list Cartesian product
-- [[[Prop]]] -> [[Prop]] where the elements are arranged in sorted order and
-- have duplicates removed, and the elements themselves are internally sorted.
disjunctList (And p q) = removeSuperDisjuncts $
                         ordCartProd $ map disjunctList [p, q]
  where ordCartProd = (foldr (Ordered.insertSet . makeDisjunct) []) . sequence
        makeDisjunct = foldr Ordered.union []
disjunctList (Or p q) = removeSuperDisjuncts $
                        Ordered.union (disjunctList p) (disjunctList q)
disjunctList p = [[p]]

removeSuperDisjuncts :: [[Prop]] -> [[Prop]]
removeSuperDisjuncts ds = filter (noSubDisjuncts ds) ds
  where noSubDisjuncts ds d = not $ any (strictSupset d) ds
        strictSupset x y = (x /= y) && (Ordered.subset y x)

cnf :: Prop -> Prop
cnf = nnf' . Not . dnf . Not
