-- Prove2me | solution 1 for Mpfx.RoundsFinite.toNegative_eq_floor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:04:34.167808+00:00
-- url     : https://prove2.me/submissions/e190bd85-8e10-4b57-b909-e721219cf5fb

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
import Theorems.Thm_Mpfx_RoundsFinite_unique_toNegative
import Theorems.Thm_Mpfx_RoundsFinite_toNegative_floor

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace RoundsFinite
theorem _root_.solution (F : FiniteFormat) (x : ℝ) {y : Dyadic}
    (hy : RoundsFinite F.unbounded .toNegative x y) :
    y = Dyadic.ofIntZpow ⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋ (F.canonicalExp x) :=
  RoundsFinite.unique_toNegative hy (RoundsFinite.toNegative_floor F x)
end RoundsFinite
end Mpfx
