module DTX

import Data.Vect
import DT
import Util

%default total

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

data DTX : DT -> Type where
  ConvX  : Conversion t1 t2 -> DTX t1
  ProdX  : DTX l -> DTX r -> DTX (Prod l r)
  SigmaX : DTX c -> ((x : interp c) -> DTX (d x)) -> DTX (Sigma c d)

copy : DTX t 
copy = ConvX idConv  

-- decoupled version of FT2.ft3
lenWord : DT
lenWord = Sigma (Leaf (Fin $ power 2 8)) (\n => Leaf (Vect (toNat n) Bool))

encodeLenWord : DTX DTX.lenWord
encodeLenWord = SigmaX (ConvX int8) (\len => copy)
  where
  encode : Fin 256 -> Vect 8 Bool
  decode : Vect 8 Bool -> Fin 256
  int8 : Conversion (Leaf (Fin $ power 2 8)) (Leaf (Vect 8 Bool))
  int8 = Convert encode (Just . decode) ?prf