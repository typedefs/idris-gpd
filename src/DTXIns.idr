module DTXIns

import Data.Vect
import DT
import Conversion
import Util

%default total
%access public export

-- 5 Inserting New Fields

data Side = LeftSide | RightSide

data DTX : (top : DT) -> DT -> Type where
  ConvX  : Conversion t1 t2 -> DTX top t1
  ProdX  : DTX top l -> DTX top r -> DTX top (Prod l r)
  SigmaX : DTX top c -> ((x : interp c) -> DTX top (d x)) -> DTX top (Sigma c d)
  InsX   : (t1 : DT) -> Side -> (interp top -> interp t1) -> DTX top t

mutual   
  extendType : {t : DT} -> DTX top t -> DT
  extendType     (ConvX {t2} _)        = t2
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
  retractValue (InsX t1 LeftSide f)    (_, it)      = Just it
  retractValue (InsX t1 RightSide f)   (it, _)      = Just it
    
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
  retractExtendId (InsX t1 LeftSide f)    itop  it         = Refl
  retractExtendId (InsX t1 RightSide f)   itop  it         = Refl

--copypaste 

copy : DTX top t
copy = ConvX idConv  

lenWord : DT
lenWord = Sigma (Leaf (Fin $ power 2 8)) (\n => Leaf (Vect (toNat n) Bool))

-- Tying the knot

DTXS : DT -> Type
DTXS t = DTX t t

extendTypeS : {t : DT} -> DTXS t -> DT
extendTypeS = extendType

extendValueS : {t : DT} -> (tx : DTXS t) -> interp t -> interp (extendTypeS tx)
extendValueS tx it = extendValue tx it it

retractValueS : {t : DT} -> (tx : DTXS t) -> interp (extendTypeS tx) -> Maybe (interp t)
retractValueS = retractValue

encodeLenWord : DTXS DTXIns.lenWord
encodeLenWord = SigmaX (ConvX int8) (\len => copy)
  where
  int8 : Conversion (Leaf (Fin $ power 2 8)) (Leaf (Vect 8 Bool))
  int8 = Convert encodeFin (Just . decodeFin) (\x => really_believe_me x)  -- YOLO

lenWordEnc : DT
lenWordEnc = extendTypeS encodeLenWord

plusChecksum : DTXS DTXIns.lenWordEnc
plusChecksum = InsX (Leaf Bool) LeftSide checksum
  where
  checksum : interp DTXIns.lenWordEnc -> Bool
  checksum (_ ** xs) = head $ parity xs

retractAndCheckS : {t : DT} -> (tx : DTXS t) -> (interp (extendTypeS tx) -> interp (extendTypeS tx) -> Bool) -> interp (extendTypeS tx) -> Maybe (interp t)
retractAndCheckS tx chk itx = 
 (retractValueS tx itx) >>= \ret => if chk itx (extendValueS tx ret) then Just ret else Nothing

-- 5.1 Beyond Top-Level Insertion
  
--vecNats : DT 
--vecNats = Sigma (Leaf Nat) (\len => Leaf (Vect len Nat))

--insertMax : DTXS DTXIns.vecNats
--insertMax = SigmaX copy iMax 
--  where 
--  maxVec : interp (DTXIns.vecNats) -> Nat
--  maxVec (it ** vs) = ?problem
--  iMax : (len : Nat) -> DTX DTXIns.vecNats (Leaf (Vect len Nat)) 
--  iMax Z     = copy 
--  iMax (S n) = InsX (Leaf Nat) RightSide maxVec 
