-- Prove2me | Theorems.Thm_Mpfx_Dyadic_exists_odd_canonical_of_precisionAtMost
-- name    : Mpfx.Dyadic.exists_odd_canonical_of_precisionAtMost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:29:50.807603+00:00
-- url     : https://prove2.me/theorems/04e5dd86-6cc4-4c99-84e5-55e82ca3d4f9
-- title:
--   Dyadic: exists odd canonical of precision At Most
-- statement:
--   For any nonzero dyadic with precision at most `p`, there's a representation
--   `y = c·2^e` with `c` odd and `|c| < 2^p`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L514-L532
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L514-L532

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Mathlib.Tactic
import Definitions.Def_Mpfx_Dyadic
set_option autoImplicit true
open Mpfx
open Mpfx.Dyadic

theorem Mpfx.Dyadic.exists_odd_canonical_of_precisionAtMost {p : ℕ} {y : Dyadic}
    (hp : precisionAtMost (p : Prec) y) (hy : (y : ℝ) ≠ 0) :
    ∃ c e : ℤ, ((y : ℝ) = c * (2 : ℝ)^e) ∧ Odd c ∧ |c| < (2 : ℤ)^p := by sorry
