-- Prove2me | solution 1 for Mpfx.RoundsFinite.toNegative_iff_awayZero_of_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:12:34.186786+00:00
-- url     : https://prove2.me/submissions/559d0be5-3b66-41b9-93ce-f67b36f7cd06

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
import Theorems.Thm_Mpfx_RoundsFinite_neg_toNegative_iff_toPositive
import Theorems.Thm_Mpfx_RoundsFinite_neg_awayZero
import Theorems.Thm_Mpfx_RoundsFinite_toPositive_iff_awayZero_of_nonneg

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace RoundsFinite
theorem _root_.solution
    (F : FiniteFormat) {x : ℝ} (hx : x ≤ 0) (y : Dyadic) :
    RoundsFinite F .toNegative x y ↔ RoundsFinite F .awayZero x y :=
  calc RoundsFinite F .toNegative x y
      ↔ RoundsFinite F .toPositive (-x) (-y) :=
        RoundsFinite.neg_toNegative_iff_toPositive F x y
    _ ↔ RoundsFinite F .awayZero (-x) (-y) :=
        RoundsFinite.toPositive_iff_awayZero_of_nonneg F (neg_nonneg.mpr hx) (-y)
    _ ↔ RoundsFinite F .awayZero x y := (RoundsFinite.neg_awayZero F x y).symm
end RoundsFinite
end Mpfx
