-- Prove2me | Theorems.Thm_Mpfx_Dyadic_not_precisionAtMost_of_odd
-- name    : Mpfx.Dyadic.not_precisionAtMost_of_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:28:58.156341+00:00
-- url     : https://prove2.me/theorems/5249e2fc-193e-4fc8-8c92-1938c31c02e6
-- title:
--   Dyadic: not precision At Most of odd
-- statement:
--   The odd canonical representation is the narrowest one: if `x = c · 2^q` with
--   `c` odd and `|c| ≥ 2^p`, then `x` does not fit in `p` digits.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L608-L620
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L608-L620

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

theorem Mpfx.Dyadic.not_precisionAtMost_of_odd {p : ℕ} {x : Dyadic} {c q : ℤ}
    (hc : Odd c) (h : (x : ℝ) = (c : ℝ) * (2 : ℝ) ^ q) (hge : (2 : ℤ) ^ p ≤ |c|) :
    ¬ precisionAtMost (p : Prec) x := by sorry
