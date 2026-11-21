-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_toPositive_floor_add_one
-- name    : Mpfx.RoundsFinite.toPositive_floor_add_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:48:32.070731+00:00
-- url     : https://prove2.me/theorems/a64abdca-209d-46cc-bc7e-7a36e27e812c
-- title:
--   Rounds Finite: to Positive floor add one
-- statement:
--   Off an integer scaled mantissa, the round-up is the successor of the floor point: the ceiling
--   is the floor plus one.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L467-L473
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L467-L473

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.toPositive_floor_add_one (F : FiniteFormat) {x : ℝ}
    (hx : (⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋ : ℝ) ≠ x * (2 : ℝ) ^ (-(F.canonicalExp x))) :
    RoundsFinite F.unbounded .toPositive x
      (Dyadic.ofIntZpow (⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋ + 1) (F.canonicalExp x)) := by sorry
