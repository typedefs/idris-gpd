module Subtree

import Data.Vect
import DT
import Conversion
import Util

%default total

-- 5.1 / Subtrees

data Subtree : (t : DT) -> DT -> Type where 
  SubFst  : Subtree t l -> Subtree t (Prod l r) 
  SubSnd  : Subtree t r -> Subtree t (Prod l r) 
  SubPi1  : Subtree t c -> Subtree t (Sigma c d) 
  SubPi2  : (x : interp c) -> Subtree t (d x) -> Subtree t (Sigma c d) 
  SubStop : Subtree t t 

subTrans : Subtree t2 t1 -> Subtree t3 t2 -> Subtree t3 t1
subTrans (SubFst l)     s32 = SubFst $ subTrans l s32
subTrans (SubSnd r)     s32 = SubSnd $ subTrans r s32
subTrans (SubPi1 p1)    s32 = SubPi1 $ subTrans p1 s32
subTrans (SubPi2 x spx) s32 = SubPi2 x (subTrans spx s32)
subTrans  SubStop       s32 = s32

data Select : Subtree t2 t1 -> interp t1 -> interp t2 -> Type where 
  SelFst  : Select s x v -> Select (SubFst s) (x, y) v
  SelSnd  : Select s y v -> Select (SubSnd s) (x, y) v 
  SelPi1  : Select s c v -> Select (SubPi1 s) (c ** dc) v
  SelPi2  : Select s d v -> Select (SubPi2 x s) (x ** d) v
  SelStop : Select SubStop t t 

data Side = LeftSide | RightSide

data DTX : (top : DT) -> (t : DT) -> (s : Subtree t top) -> Type where 
  ConvX  : Conversion t1 t2 -> DTX top t1 s
  ProdX  : DTX top l (subTrans s (SubFst SubStop)) -> DTX top r (subTrans s (SubSnd SubStop)) -> DTX top (Prod l r) s
  SigmaX : DTX top c (subTrans s (SubPi1 SubStop)) -> ((x : interp c) -> DTX top (d x) (subTrans s (SubPi2 x SubStop))) -> DTX top (Sigma c d) s
  InsX   : (t1 : DT) -> Side -> ((d : interp top) -> (v : interp t) -> Select s d v -> interp t1) -> DTX top t s
