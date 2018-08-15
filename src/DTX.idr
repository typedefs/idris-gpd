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
  int8 : Conversion (Leaf (Fin $ power 2 8)) (Leaf (Vect 8 Bool))
  int8 = Convert encode (Just . decode) (\x => really_believe_me x)  -- YOLO

mutual   
  extendType : {t : DT} -> DTX t -> DT
  extendType (ConvX {t2} c)     = t2
  extendType (ProdX dl dr)      = Prod (extendType dl) (extendType dr)
  extendType (SigmaX {d} dc df) = Sigma (extendType dc) (\iedc => maybe (Leaf Void) (\it => extendType (df it)) (retractValue dc iedc))

  retractValue : {t : DT} -> (tx : DTX t) -> interp (extendType tx) -> Maybe (interp t)
  retractValue (ConvX (Convert d u f))  ietx        = u ietx
  retractValue (ProdX dl dr)           (ietl, ietr) = [| MkPair (retractValue dl ietl) (retractValue dr ietr) |]
  retractValue (SigmaX {d} dc df)      (it ** ietx) = let tt = retractValue dc it in ?wot

  extendValue : {t : DT} -> (tx : DTX t) -> interp t -> interp (extendType tx)
  extendValue (ConvX (Convert d u f))  it         = d it
  extendValue (ProdX dl dr)           (il, ir)    = (extendValue dl il, extendValue dr ir)
  extendValue (SigmaX dc df)          (it ** idt) = (extendValue dc it ** ?wut)

  retractExtendId : {t : DT} -> (tx : DTX t) -> (d : interp t) -> retractValue tx (extendValue tx d) = Just d
  retractExtendId (ConvX (Convert _ _ f)) d = f d
  retractExtendId (ProdX dl dr)  (il, ir) = 
    rewrite retractExtendId dl il in 
    rewrite retractExtendId dr ir in 
    Refl
  retractExtendId (SigmaX dc df) (it ** idt) = ?wat