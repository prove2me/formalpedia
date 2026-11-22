-- Prove2me | solution 1 for Mpfx.RoundsFinite.toPositive_floor_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:11:32.696707+00:00
-- url     : https://prove2.me/submissions/a985f3ae-6e56-45aa-ae22-6734f659bd22

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
import Theorems.Thm_Mpfx_RoundsFinite_toPositive_ceil

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace RoundsFinite
theorem _root_.solution (F : FiniteFormat) {x : ℝ}
    (hx : (⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋ : ℝ) ≠ x * (2 : ℝ) ^ (-(F.canonicalExp x))) :
    RoundsFinite F.unbounded .toPositive x
      (Dyadic.ofIntZpow (⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋ + 1) (F.canonicalExp x)) := by
  have h := RoundsFinite.toPositive_ceil F x
  rwa [le_antisymm (Int.ceil_le_floor_add_one _)
    (Int.lt_ceil.mpr (lt_of_le_of_ne (Int.floor_le _) hx))] at h
end RoundsFinite
end Mpfx
