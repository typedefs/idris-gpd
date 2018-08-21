module Conversion

import Data.Vect
import DT
import Util

%default total
%access public export

-- shared from chapter 4

data Conversion : (t1, t2 : DT) -> Type where 
  Convert : (d : interp t1 -> interp t2) 
         -> (u : interp t2 -> Maybe (interp t1)) 
         -> ((x : interp t1) -> u (d x) = Just x) 
         -> Conversion t1 t2 
      
idConv : Conversion t t 
idConv = Convert id (Just . id) (\x => Refl)

compConv : Conversion a b -> Conversion b c -> Conversion a c
compConv (Convert ab ba prf1) (Convert bc cb prf2) = 
  Convert (bc . ab) (\cc => cb cc >>= ba) 
    (\x => rewrite prf2 (ab x) in prf1 x)
  