import Data.List

data Term = Bare Var
          | UIFn Fn [Term]

data Var = Var String deriving (Eq)

data Fn = Fn String

data Pred = Pred String

data Prop = Const Bool
          | Atom Pred [Term]
          | Not Prop
          | And Prop Prop
          | Or Prop Prop
          | Imp Prop Prop
          | Iff Prop Prop
          | Forall Var Prop
          | Exists Var Prop

instance Show Prop where
  show (Const True) = "⊤"
  show (Const False) = "⊥"
  show (Atom (Pred s) ts) = showPred s ts
  show (Not p) = "¬" ++ (show p)
  show (And p1 p2) = "(" ++ (show p1) ++ " ∧ " ++ (show p2) ++ ")"
  show (Or p1 p2) = "(" ++ (show p1) ++ " ∨ " ++ (show p2) ++ ")"
  show (Imp p1 p2) = "(" ++ (show p1) ++ " → " ++ (show p2) ++ ")"
  show (Iff p1 p2) = "(" ++ (show p1) ++ " ↔ " ++ (show p2) ++ ")"
  show (Forall (Var s) p) = "(∀" ++ s ++ ". " ++ (show p) ++ ")"
  show (Exists (Var s) p) = "(∃" ++ s ++ ". " ++ (show p) ++ ")"

showPred :: String -> [Term] -> String
showPred "=" (x:y:[]) = "(" ++ (show x) ++ "=" ++ (show y) ++ ")"
showPres s ts = s ++ "(" ++ (intercalate ", " $ map show ts) ++ ")"

instance Show Term where
  show (Bare (Var s)) = s
  show (UIFn (Fn s) ts) = showFn s ts

showFn :: String -> [Term] -> String
showFn "*" (x:y:[]) = "(" ++ (show x) ++ "*" ++ (show y) ++ ")"
showFn s ts = s ++ "(" ++ (intercalate ", " $ map show ts) ++ ")"

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

infix 5 ===
(===) :: Term -> Term -> Prop
t1 === t2 = Atom (Pred "=") [t1, t2]

infixr 7 /*/
(/*/) :: Term -> Term -> Term
t1 /*/ t2 = UIFn (Fn "*") [t1, t2]

termval :: (Fn -> ([d] -> d)) -> (Var -> d) -> Term -> d
termval fM v t = case t of
  Bare var  -> v var
  UIFn f ts -> (fM f) $ map (termval fM v) ts

holds :: [d] -> (Fn -> ([d] -> d)) -> (Pred -> ([d] -> Bool)) -> (Var -> d)
         -> Prop -> Bool
holds dom fM pM v p = case p of
  Const   b    -> b
  Atom pred ts -> (pM pred) $ map (termval fM v) ts
  Not p'       -> not $ holds dom fM pM v p'
  And p1 p2    -> (holds dom fM pM v p1) && (holds dom fM pM v p2)
  Or p1 p2     -> (holds dom fM pM v p1) || (holds dom fM pM v p2)
  Imp p1 p2    -> (not $ holds dom fM pM v p1) || (holds dom fM pM v p2)
  Iff p1 p2    -> (holds dom fM pM v p1) == (holds dom fM pM v p2)
  Forall x p'  -> all (\x' -> holds dom fM pM (v' x') p') dom
    where v' x' var = if var == x then x' else v var
  Exists x p'  -> any (\x' -> holds dom fM pM (v' x') p') dom
    where v' x' var = if var == x then x' else v var

boolDom = [False, True]

boolFM :: Fn -> ([Bool] -> Bool)
boolFM (Fn "0") [] = False
boolFM (Fn "1") [] = True
boolFM (Fn "+") (x:y:[]) = not $ x == y
boolFM (Fn "*") (x:y:[]) = x && y

boolPM :: Pred -> ([Bool] -> Bool)
boolPM (Pred "=") (x:y:[]) = x == y

trueBoolExpr = Forall (Var "x") $ (Not $ (Bare $ Var "x") === UIFn (Fn "0") [])
               ==> (Exists (Var "y") $
               ((Bare $ Var "x") /*/ (Bare $ Var "y")) === (UIFn (Fn "1") []))

falseBoolExpr = Exists (Var "x") $ Forall (Var "y") $
                (UIFn (Fn "*") [Bare $ Var "x", Bare $ Var "y"]) ===
                (UIFn (Fn "1") [])
