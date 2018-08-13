module Util

import Data.Vect

%access public export
%default total

splitList : (k : Nat) -> List Bool -> Vect m Bool -> Maybe (Vect (k+m) Bool, List Bool)
splitList {m}  Z    rem        acc = Just (reverse acc, rem)
splitList     (S _) []         _   = Nothing
splitList {m} (S l) (r :: rem) acc = rewrite plusCommutative 1 (l+m) in 
                                     rewrite sym $ plusAssociative l m 1 in 
                                     rewrite plusCommutative m 1 in 
                                     splitList l rem (r :: acc) 

toNat : Vect n Bool -> Nat
toNat xs = go xs Z
  where 
  go : Vect k Bool -> Nat -> Nat
  go [] acc = acc
  go (True :: xs) acc = go xs (S (2 * acc))
  go (False :: xs) acc = go xs (2 * acc)                                     