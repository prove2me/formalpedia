-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_numDigits_extend
-- name    : Mpfx.FiniteFormat.numDigits_extend
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:59:40.054567+00:00
-- url     : https://prove2.me/theorems/1bcd0a66-217d-4779-9686-8b091922cace
-- title:
--   Finite Format: num Digits extend
-- statement:
--   **Digit-shift lemma** (`w₂ = w₁ + k`): extending `F` by `k` increases the digit count of every
--   nonzero `x` by exactly `k`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L542-L544
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L542-L544

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.numDigits_extend (F : FiniteFormat) (k : ℕ) {x : ℝ} (hx : x ≠ 0) :
    (F.extend k).numDigits x = F.numDigits x + k := by sorry
