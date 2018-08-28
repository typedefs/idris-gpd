module DT

import Data.Vect
import Util

%access public export
%default total

-- 3 Beyond Bits

mutual 
  data DT : Type where
    Leaf  : Type -> DT
    Prod  : DT -> DT -> DT
    Sigma : (t : DT) -> (interp t -> DT) -> DT
    
  interp : DT -> Type
  interp (Leaf a)     = a
  interp (Prod t1 t2) = (interp t1, interp t2)
  interp (Sigma t f)  = (it : interp t ** interp (f it))

-- 3.1 Low-Level Descriptions

data IsLowLevel : DT -> Type where
  LeafILL  : IsLowLevel (Leaf (Vect n Bool))  
  ProdILL  : IsLowLevel l -> IsLowLevel r -> IsLowLevel (Prod l r)
  SigmaILL : IsLowLevel c -> ((x : interp c) -> IsLowLevel (f x)) -> IsLowLevel (Sigma c f)

parse : IsLowLevel t -> List Bool -> Maybe (interp t, List Bool)  
parse (LeafILL {n})        bs = splitList n bs []
parse (ProdILL ill1 ill2)  bs = do (x1, r1) <- parse ill1 bs
                                   (x2, r2) <- parse ill2 r1
                                   pure $ ((x1, x2), r2)
parse (SigmaILL illx illf) bs with (parse illx bs)
  parse (SigmaILL illx illf) bs | Just (y, rem) = do (fy, r2) <- assert_total $ parse (illf y) rem
                                                     pure $ ((y**fy), r2)
  parse (SigmaILL illx illf) bs | Nothing = Nothing

pp : IsLowLevel t -> interp t -> List Bool
pp  LeafILL             is          = toList is
pp (ProdILL ill1 ill2)  (x1, x2)    = pp ill1 x1 ++ pp ill2 x2
pp (SigmaILL illx illf) (ix ** ifx) = pp illx ix ++ pp (illf ix) ifx

-- 3.2 A High-Level Example

data Tag = Boolean | Floating

taggedUnion : DT
taggedUnion = Sigma (Leaf Tag) contents
  where
  contents : Tag -> DT
  contents Boolean = Leaf Bool
  contents Floating = Leaf Double

{-
roundTrip : {t : DT} -> (ill : IsLowLevel t) -> (d : interp t) -> (rem : List Bool) -> parse ill (pp ill d ++ rem) = Just (d, rem) 
roundTrip LeafILL           []        rem = Refl
roundTrip LeafILL           (x :: xs) rem = ?wat1
roundTrip (ProdILL l r)     (il, ir)  rem = ?wat2
roundTrip (SigmaILL ic ifc) (it**fit) rem = 
  rewrite sym $ appendAssociative (pp ic it) (pp (ifc it) fit) rem in 
  rewrite roundTrip ic it (pp (ifc it) fit ++ rem) in
  rewrite roundTrip (ifc it) fit rem in  -- breaks here
  ?wat3
-}