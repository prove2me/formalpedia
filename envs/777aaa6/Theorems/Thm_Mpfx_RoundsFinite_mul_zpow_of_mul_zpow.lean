-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_mul_zpow_of_mul_zpow
-- name    : Mpfx.RoundsFinite.mul_zpow_of_mul_zpow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:57:17.253722+00:00
-- url     : https://prove2.me/theorems/067642db-82ab-4d49-aae1-cbbfb5325cbe
-- title:
--   Rounds Finite: mul zpow of mul zpow
-- statement:
--   Rounding keeps a quantum: if `x` is a multiple of `2ᵏ`, so is its rounding.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L362-L373
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L362-L373

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.mul_zpow_of_mul_zpow {F : FiniteFormat} {rm : RoundingMode} {x : ℝ}
    {y : Dyadic} (h : RoundsFinite F.unbounded rm x y) {z k : ℤ} (hx : x = z * (2 : ℝ) ^ k) :
    ∃ c : ℤ, (y : ℝ) = c * (2 : ℝ) ^ k := by sorry
