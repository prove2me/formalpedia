-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_toNegative_iff_awayZero_of_nonpos
-- name    : Mpfx.RoundsFinite.toNegative_iff_awayZero_of_nonpos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:43:57.349168+00:00
-- url     : https://prove2.me/theorems/c6570e8b-c5de-4f39-9907-ed7d6cab91d7
-- title:
--   Rounds Finite: to Negative iff away Zero of nonpos
-- statement:
--   For `x ≤ 0`, rounding toward `−∞` coincides with rounding away from zero
--   (both move to the more-negative side). Sign-mirror of
--   `toPositive_iff_awayZero_of_nonneg`, derived via joint negation.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L197-L205
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L197-L205

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.toNegative_iff_awayZero_of_nonpos
    (F : FiniteFormat) {x : ℝ} (hx : x ≤ 0) (y : Dyadic) :
    RoundsFinite F .toNegative x y ↔ RoundsFinite F .awayZero x y := by sorry
