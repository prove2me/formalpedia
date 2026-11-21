-- Prove2me | Theorems.Thm_Mpfx_Dyadic_le_log_of_quantum
-- name    : Mpfx.Dyadic.le_log_of_quantum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:28:14.195193+00:00
-- url     : https://prove2.me/theorems/3e02aaa8-cd24-486f-b6be-009943fdf6c7
-- title:
--   Dyadic: le log of quantum
-- statement:
--   A nonzero dyadic with `quantumAtLeast e` lies at or above binade `e`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L400-L404
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L400-L404

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

theorem Mpfx.Dyadic.le_log_of_quantum {e : ℤ} {d : Dyadic}
    (hq : quantumAtLeast (e : QExp) d) (hne : (d : ℝ) ≠ 0) :
    e ≤ Int.log 2 |(d : ℝ)| := by sorry
