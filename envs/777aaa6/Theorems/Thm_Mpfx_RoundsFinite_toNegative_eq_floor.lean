-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_toNegative_eq_floor
-- name    : Mpfx.RoundsFinite.toNegative_eq_floor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:56:14.326538+00:00
-- url     : https://prove2.me/theorems/3542db41-3509-4d70-abea-7cc79f6d8062
-- title:
--   Rounds Finite: to Negative eq floor
-- statement:
--   Any round-down of `x` *is* that floor point.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L476-L479
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L476-L479

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.toNegative_eq_floor (F : FiniteFormat) (x : ℝ) {y : Dyadic}
    (hy : RoundsFinite F.unbounded .toNegative x y) :
    y = Dyadic.ofIntZpow ⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋ (F.canonicalExp x) := by sorry
