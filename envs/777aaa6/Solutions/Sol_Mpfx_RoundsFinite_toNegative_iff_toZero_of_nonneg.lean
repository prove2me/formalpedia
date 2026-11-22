-- Prove2me | solution 1 for Mpfx.RoundsFinite.toNegative_iff_toZero_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:11:30.128882+00:00
-- url     : https://prove2.me/submissions/de2343d1-8ea2-4f99-8df0-7ff2b3c846ab

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
import Theorems.Thm_Mpfx_RoundsFinite_neg_toZero
import Theorems.Thm_Mpfx_RoundsFinite_neg_toNegative_iff_toPositive
import Theorems.Thm_Mpfx_RoundsFinite_toPositive_iff_toZero_of_nonpos

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace RoundsFinite
theorem _root_.solution
    (F : FiniteFormat) {x : ℝ} (hx : 0 ≤ x) (y : Dyadic) :
    RoundsFinite F .toNegative x y ↔ RoundsFinite F .toZero x y :=
  calc RoundsFinite F .toNegative x y
      ↔ RoundsFinite F .toPositive (-x) (-y) :=
        RoundsFinite.neg_toNegative_iff_toPositive F x y
    _ ↔ RoundsFinite F .toZero (-x) (-y) :=
        RoundsFinite.toPositive_iff_toZero_of_nonpos F (neg_nonpos.mpr hx) (-y)
    _ ↔ RoundsFinite F .toZero x y := (RoundsFinite.neg_toZero F x y).symm
end RoundsFinite
end Mpfx
