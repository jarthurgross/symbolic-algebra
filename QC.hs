import Prop
import Test.QuickCheck
import Control.Monad

prop_nnf = forAll prop $ (\p -> tautology $ p <=> (nnf p))
prop_dnf = forAll prop $ (\p -> tautology $ p <=> (dnf p))
prop_cnf = forAll prop $ (\p -> tautology $ p <=> (cnf p))

prop = sized prop'
prop' 0 = oneof [liftM Const arbitrary, liftM Atom singleChar]
prop' n | n > 0 = oneof [ liftM Not subprop
                        , liftM2 And subprop subprop
                        , liftM2 Or subprop subprop
                        , liftM2 Imp subprop subprop
                        , liftM2 Iff subprop subprop
                        ]
  where subprop = prop' (n `div` 2)
singleChar = oneof $ map (\x -> return [x]) ['p'..'z']
