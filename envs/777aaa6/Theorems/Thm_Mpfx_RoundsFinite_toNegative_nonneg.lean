-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_toNegative_nonneg
-- name    : Mpfx.RoundsFinite.toNegative_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:44:44.500356+00:00
-- url     : https://prove2.me/theorems/5197efa1-4416-4fc4-8d7e-f575d0b6764f
-- title:
--   Rounds Finite: to Negative nonneg
-- statement:
--   `0 ∈ F` is a candidate (Flocq `round_pred_ge_0`).
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L642-L645
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L642-L645

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.toNegative_nonneg {F : FiniteFormat} {x : ℝ} (hx : 0 ≤ x)
    {y : Dyadic} (h : RoundsFinite F .toNegative x y) : (0 : ℝ) ≤ (y : ℝ) := by sorry
