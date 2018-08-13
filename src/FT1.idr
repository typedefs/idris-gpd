module FT1

import Data.Vect
import Util

%default total

data FT : Type where
  Word : Nat -> FT
  Prod : FT -> FT -> FT
  
ft1 : FT
ft1 = Word 32 `Prod` Word 32  

interp : FT -> Type
interp (Word n)     = Vect n Bool
interp (Prod t1 t2) = (interp t1, interp t2)

parse : (f : FT) -> List Bool -> Maybe (interp f, List Bool)
parse (Word n)     xs = rewrite plusCommutative 0 n in splitList n xs []
parse (Prod t1 t2) xs = do (x1, r1) <- parse t1 xs
                           (x2, r2) <- parse t2 r1
                           pure $ ((x1, x2), r2)

pp : (f : FT) -> interp f -> List Bool
pp (Word n)     bs       = toList bs
pp (Prod t1 t2) (x1, x2) = pp t1 x1 ++ pp t2 x2

--roundTrip' : (f : FT) -> (x : interp f) -> (rem : List Bool) -> parse f (pp f x ++ rem) = Just (x, rem)