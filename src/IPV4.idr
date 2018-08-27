module IPV4

import Data.Vect
import DT
import DTXIns
import Conversion
import Util

%default total

-- 6.1 The Initial Description

data ECN = NonECT | ECT0 | ECT1 | CE

ECN2Bit : ECN -> Vect 2 Bool
ECN2Bit NonECT = [True,  True ]
ECN2Bit ECT0   = [False, True ]
ECN2Bit ECT1   = [True,  False]
ECN2Bit CE     = [False, False]

Bit2ECN : Vect 2 Bool -> ECN
Bit2ECN [True,  True ] = NonECT
Bit2ECN [False, True ] = ECT0  
Bit2ECN [True,  False] = ECT1  
Bit2ECN [False, False] = CE

Lengths : Type
Lengths = (dl ** ol ** (LTE ol 10, LT (4 * (5 + ol) + dl) (pow 2 2)))  -- TODO should be 2^16, use Biz/BizMod2? 

IPv4Type : DT
IPv4Type = Sigma header1 optData
  where
  header1 : DT
  header1 = Prod (Leaf Lengths) $ 
            Prod (Leaf ECN) $            -- ECN
            Prod (Leaf (Vect 32 Bool))   -- Source
                 (Leaf (Vect 32 Bool))   -- Destination
  optData : interp header1 -> DT
  optData ((dl ** ol ** _), _, _, _) = Prod (Leaf (Vect (32*ol) Bool)) (Leaf (Vect (8*dl) Bool))

-- 6.2 Transformations

mix : (tx : DTX (Prod l r) r) -> (rf : interp (extendType tx) -> Maybe (interp l)) -> ((d1 : interp l) -> (d2 : interp r) -> rf (extendValue tx (d1, d2) d2) = Just d1) -> DTX top (Prod l r)
mix tx rf f = ?wat
