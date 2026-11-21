-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_toNegative_iff_toZero_of_nonneg
-- name    : Mpfx.RoundsFinite.toNegative_iff_toZero_of_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:43:23.481905+00:00
-- url     : https://prove2.me/theorems/defc64e3-9d9f-4f6e-b47a-f8f5cece32ce
-- title:
--   Rounds Finite: to Negative iff to Zero of nonneg
-- statement:
--   For `0 ≤ x`, rounding toward `−∞` coincides with rounding toward zero
--   (both move down). Sign-mirror of `toPositive_iff_toZero_of_nonpos`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L209-L217
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L209-L217

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.toNegative_iff_toZero_of_nonneg
    (F : FiniteFormat) {x : ℝ} (hx : 0 ≤ x) (y : Dyadic) :
    RoundsFinite F .toNegative x y ↔ RoundsFinite F .toZero x y := by sorry
