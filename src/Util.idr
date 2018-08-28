module Util

import Data.Bits
import Data.Fin
import Data.Vect

%access public export
%default total

splitList : (k : Nat) -> List Bool -> Vect m Bool -> Maybe (Vect (m+k) Bool, List Bool)
splitList {m}  Z    rem        acc = Just (rewrite plusCommutative m 0 in reverse acc, rem)
splitList     (S _) []         _   = Nothing
splitList {m} (S l) (r :: rem) acc = rewrite plusAssociative m 1 l in 
                                     rewrite plusCommutative m 1 in 
                                     splitList l rem (r :: acc)

parity : Vect n Bool -> Vect 1 Bool
parity xs = [foldr (/=) False xs]

toNat : Vect n Bool -> Nat
toNat xs = go xs Z
  where 
  go : Vect k Bool -> Nat -> Nat
  go [] acc = acc
  go (True :: xs) acc = go xs (S (2 * acc))
  go (False :: xs) acc = go xs (2 * acc)

-- aka `tabulate`, exists in Control.Isomorphism.Vect in post 1.3 stdlib
unindex : (Fin n -> a) -> Vect n a
unindex {n = Z} _ = []
unindex {n = S k} f = f FZ :: unindex (f . FS)

encodeFin : Fin (power 2 n) -> Vect n Bool
encodeFin {n} f = 
  let bits = intToBits {n} $ finToInteger f in 
  reverse $ unindex (\f => getBit f bits)

powerNotZ : (n : Nat) -> (k ** power 2 n = S k)
powerNotZ  Z    = (Z ** Refl)
powerNotZ (S n) = 
  let (k ** prf) = powerNotZ n in 
  rewrite prf in 
  rewrite plusCommutative k 0 in
  (k + (S k) ** Refl)  

decodeFin : Vect n Bool -> Fin (power 2 n)
decodeFin {n} vs = let (k ** prf) = powerNotZ n in 
                fromMaybe (rewrite prf in the (Fin (S k)) FZ) $ 
                natToFin (toNat vs) (power 2 n)

vecMax : Vect (S n) Nat -> Nat
vecMax (v::vs) = go v vs
  where
  go : Nat -> Vect k Nat -> Nat
  go a [] = a
  go a (x::xs) = if x>a then go x xs else go a xs
