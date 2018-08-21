module DTXIns

import Data.Vect
import DT
import Conversion
import Util

%default total

-- 5 Inserting New Fields

data Side = LeftSide | RightSide

data DTX : (top : DT) -> DT -> Type where
  ConvX  : Conversion t1 t2 -> DTX top t1
  ProdX  : DTX top l -> DTX top r -> DTX top (Prod l r)
  SigmaX : DTX top c -> ((x : interp c) -> DTX top (d x)) -> DTX top (Sigma c d)
  InsX   : (t1 : DT) -> Side -> (interp top -> interp t1) -> DTX top t

mutual   
  extendType : {t : DT} -> DTX top t -> DT
  extendType     (ConvX {t2} c)        = t2
  extendType     (ProdX dl dr)         = Prod (extendType dl) (extendType dr)
  extendType     (SigmaX dc df)        = Sigma (extendType dc) (\iedc => maybe (Leaf Void) (\it => extendType (df it)) (assert_total $ retractValue dc iedc))  -- YOLO
  extendType {t} (InsX t1 LeftSide _)  = Prod t1 t
  extendType {t} (InsX t1 RightSide _) = Prod t t1

  retractValue : {t : DT} -> (tx : DTX top t) -> interp (extendType tx) -> Maybe (interp t)
  retractValue (ConvX (Convert _ u _))  ietx        = u ietx
  retractValue (ProdX dl dr)           (ietl, ietr) = [| MkPair (retractValue dl ietl) (retractValue dr ietr) |]
  retractValue (SigmaX dc df)          (it ** ietx) with (retractValue dc it)
    retractValue (SigmaX dc df) (it ** ietx) | Just ic = map (\x => (ic ** x)) (retractValue (df ic) ietx)
    retractValue (SigmaX dc df) (it ** ietx) | Nothing = absurd ietx  
  retractValue (InsX t1 LeftSide f)   (_, it) = Just it
  retractValue (InsX t1 RightSide f)  (it, _) = Just it
    
mutual
  extendValue : {t : DT} -> (tx : DTX top t) -> interp top -> interp t -> interp (extendType tx)
  extendValue (ConvX (Convert d _ _)) _     it         = d it
  extendValue (ProdX dl dr)           itop (il, ir)    = (extendValue dl itop il, extendValue dr itop ir)
  extendValue (SigmaX dc df)          itop (it ** idt) = (extendValue dc itop it ** rewrite retractExtendId dc itop it in extendValue (df it) itop idt)
  extendValue (InsX t1 LeftSide f)    itop  it         = (f itop, it)
  extendValue (InsX t1 RightSide f)   itop  it         = (it, f itop)

  retractExtendId : {t : DT} -> (tx : DTX top t) -> (itop : interp top) -> (it : interp t) -> retractValue tx (extendValue tx itop it) = Just it
  retractExtendId (ConvX (Convert _ _ f)) itop  it         = f it
  retractExtendId (ProdX dl dr)           itop (il, ir)    = 
    rewrite retractExtendId dl itop il in 
    rewrite retractExtendId dr itop ir in 
    Refl
  retractExtendId (SigmaX {c} dc df)      itop (it ** idt) = 
    --rewrite retractExtendId {t=c} dc itop it in
    really_believe_me ()   
  retractExtendId (InsX t1 LeftSide f)   itop   it         = Refl
  retractExtendId (InsX t1 RightSide f)  itop   it         = Refl