-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_abs_lt_of_mul_zpow_canonicalExp
-- name    : Mpfx.FiniteFormat.abs_lt_of_mul_zpow_canonicalExp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:29:15.465694+00:00
-- url     : https://prove2.me/theorems/807a4ac4-21ac-4ccf-b2f1-711dbd253f70
-- title:
--   Finite Format: abs lt of mul zpow canonical Exp
-- statement:
--   A multiple `m · 2^canonicalExp x` of a nonzero `x` has `|m| < 2^p`:
--   `|x| < 2^(⌊log₂|x|⌋ + 1) ≤ 2^(p + canonicalExp x)`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L529-L540
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L529-L540

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx

theorem Mpfx.FiniteFormat.abs_lt_of_mul_zpow_canonicalExp (F : FiniteFormat) {p : ℕ}
    (hp : F.p = (p : Prec)) {x : ℝ} (hx : x ≠ 0) {m : ℤ}
    (h : x = m * (2 : ℝ) ^ F.canonicalExp x) : |m| < 2 ^ p := by sorry
