-- Prove2me | solution 1 for Mpfx.Dyadic.coe_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:26:36.610425+00:00
-- url     : https://prove2.me/submissions/985d4e57-fbde-439e-813a-9f7eacb97cd5

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Mathlib.Tactic
import Definitions.Def_Mpfx_Dyadic
import Theorems.Thm_Mpfx_Dyadic_coe_real_eq_ratCast
import Theorems.Thm_Mpfx_Dyadic_coe_real_neg
attribute [local simp] Mpfx.Dyadic.coe_real_neg
attribute [local norm_cast] Mpfx.Dyadic.coe_real_neg

set_option autoImplicit true
open Mpfx
open Mpfx.Dyadic
namespace Mpfx.Dyadic
theorem _root_.solution (x : Dyadic) : (Dyadic.abs x : ℝ) = |(x : ℝ)| := by
  unfold Dyadic.abs
  by_cases h : 0 ≤ (x : ℚ)
  · rw [if_pos h]
    rw [coe_real_eq_ratCast]
    have : (0 : ℝ) ≤ ((x : ℚ) : ℝ) := by exact_mod_cast h
    rw [_root_.abs_of_nonneg this]
  · rw [if_neg h]
    rw [coe_real_neg, coe_real_eq_ratCast]
    have : ((x : ℚ) : ℝ) < 0 := by
      have : (x : ℚ) < 0 := lt_of_not_ge h
      exact_mod_cast this
    rw [_root_.abs_of_neg this]
end Mpfx.Dyadic
