-- Prove2me | Theorems.Thm_Mpfx_Dyadic_abs_ge_two_zpow_of_quantum
-- name    : Mpfx.Dyadic.abs_ge_two_zpow_of_quantum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:28:47.142174+00:00
-- url     : https://prove2.me/theorems/708abbd7-d54a-45ae-b79c-a5a4336f0802
-- title:
--   Dyadic: abs ge two zpow of quantum
-- statement:
--   A nonzero dyadic with `quantumAtLeast e` has absolute value at least `2^e`.
--   The smallest nonzero significand `c` is `±1`, giving `|c·2^e| = 2^e`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L389-L397
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L389-L397

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

theorem Mpfx.Dyadic.abs_ge_two_zpow_of_quantum {e : ℤ} {d : Dyadic}
    (hq : quantumAtLeast (e : QExp) d) (hne : (d : ℝ) ≠ 0) :
    (2 : ℝ)^e ≤ |(d : ℝ)| := by sorry
