-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_exists_mul_zpow_canonicalExp
-- name    : Mpfx.FiniteFormat.exists_mul_zpow_canonicalExp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:25:29.304597+00:00
-- url     : https://prove2.me/theorems/ca82ccf5-8246-4c9b-b753-5e40c32b625d
-- title:
--   Finite Format: exists mul zpow canonical Exp
-- statement:
--   **Every value is a multiple of `2^canonicalExp`**: `z = m · 2^cexp z`.
--   Each constraint of the format makes `z` a multiple of its own exponent — the
--   precision term `⌊log₂|z|⌋ + 1 − p` and the minimum quantum — and `canonicalExp`
--   is the larger of the two.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L493-L525
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L493-L525

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx

theorem Mpfx.FiniteFormat.exists_mul_zpow_canonicalExp (F : FiniteFormat) {z : Dyadic}
    (hz : z ∈ F.unbounded) : ∃ m : ℤ, (z : ℝ) = m * (2 : ℝ) ^ F.canonicalExp z := by sorry
