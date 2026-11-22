-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_unique_toZero
-- name    : Mpfx.RoundsFinite.unique_toZero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:55:52.334566+00:00
-- url     : https://prove2.me/theorems/e2771e9a-c163-4f0d-bae2-a2a5bae02525
-- title:
--   Rounds Finite: unique to Zero
-- statement:
--   RTZ agrees with round-down on `0 ≤ x` and round-up on `x ≤ 0`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L239-L248
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L239-L248

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.unique_toZero {F : FiniteFormat} {x : ℝ} {y₁ y₂ : Dyadic}
    (h₁ : RoundsFinite F .toZero x y₁) (h₂ : RoundsFinite F .toZero x y₂) :
    y₁ = y₂ := by sorry
