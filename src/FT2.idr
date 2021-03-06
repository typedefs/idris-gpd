module FT2

import Data.Vect
import Util

%default total

-- 2.1 Beyond Simple Universes

mutual
  data FT : Type where
    Word  : Nat -> FT
    Prod  : FT -> FT -> FT
    Calc  : (t : FT) -> interp t -> FT
    Sigma : (t : FT) -> (interp t -> FT) -> FT

  interp : FT -> Type
  interp (Word n)     = Vect n Bool
  interp (Prod t1 t2) = (interp t1, interp t2)
  interp (Calc t v)   = ()
  interp (Sigma t f)  = (it : interp t ** interp (f it))

semidec : (t : FT) -> (x, y : interp t) -> Maybe (x = y)
semidec (Word n) x y = case decEq x y of
                         Yes prf => Just prf
                         No _ => Nothing
semidec (Prod t1 t2) (x1, x2) (y1, y2) with (semidec t1 x1 y1, semidec t2 x2 y2)
  semidec (Prod t1 t2) (x1, x2) (x1, x2) | (Just Refl, Just Refl) = Just Refl
  semidec (Prod t1 t2) (x1, x2) (y1, y2) | _ = Nothing
semidec (Calc t v) () () = Just Refl
semidec (Sigma t f) (ix ** fx) (iy ** fy) with (semidec t ix iy)
  semidec (Sigma t f)  (ix ** fx) (ix ** fy) | Just Refl with (semidec (f ix) fx fy)
    semidec (Sigma t f)  (ix ** fx) (ix ** fx) | Just Refl | Just Refl = Just Refl
    semidec (Sigma t f)  (ix ** fx) (ix ** fy) | Just Refl | Nothing = Nothing
  semidec (Sigma t f)  (ix ** fx) (iy ** fy) | Nothing = Nothing

ft2 : FT
ft2 = Sigma (Word 8) (\d => Calc (Word 1) (parity d))

parse : (f : FT) -> List Bool -> Maybe (interp f, List Bool)
parse (Word n)     bs = splitList n bs []
parse (Prod t1 t2) bs = do (x1, r1) <- parse t1 bs
                           (x2, r2) <- parse t2 r1
                           pure $ ((x1, x2), r2)
parse (Calc t v) bs with (parse t bs)
  parse (Calc t v) bs | Just (y, rem) with (semidec t y v)
    parse (Calc t v) bs | Just (v, rem) | Just Refl = Just ((), rem)
    parse (Calc t v) bs | Just (y, rem) | Nothing = Nothing
  parse (Calc t v) bs | Nothing = Nothing
parse (Sigma t f) bs with (parse t bs)
  parse (Sigma t f) bs | Just (y, rem) = do (fy, r2) <- assert_total $ parse (f y) rem
                                            pure $ ((y**fy), r2)
  parse (Sigma t f) bs | Nothing = Nothing

pp : (f : FT) -> interp f -> List Bool
pp (Word n)     bs         = toList bs
pp (Prod t1 t2) (x1, x2)   = pp t1 x1 ++ pp t2 x2
pp (Calc t v)   ()         = pp t v
pp (Sigma t f)  (ix ** fx) = pp t ix ++ pp (f ix) fx

ft3 : FT
ft3 = Sigma (Word 8) (\d => Word (toNat d))

--roundTrip' : (f : FT) -> (x : interp f) -> (rem : List Bool) -> parse f (pp f x ++ rem) = Just (x, rem)
