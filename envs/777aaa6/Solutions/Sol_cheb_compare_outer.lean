-- Prove2me | solution 1 for cheb_compare_outer
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-09T11:59:36.250501+00:00
-- url     : https://prove2.me/submissions/8d3fdc29-fe85-4112-b4ce-dced3a4fbb47
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_cheb_compare_outer
import Theorems.Thm_cheb_alt_compare
import Theorems.Thm_jordan_cos_sq_le
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Polynomial Polynomial.Chebyshev Real

theorem solution : cheb_compare_outer := by
  intro p d hd1 hd h c hc1 hc2 hcase
  have hdr_pos : (0 : ℝ) < (d : ℝ) := by
    have : (1 : ℕ) ≤ d := hd1
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  -- d² > 0, so from d²(1-c²) ≤ 1, get 1-c² ≤ 1/d², i.e., c² ≥ 1-1/d².
  have hd2_pos : (0 : ℝ) < (d : ℝ)^2 := by positivity
  have hc2ge : (1 : ℝ) - 1/(d : ℝ)^2 ≤ c^2 := by
    have h1 : 1 - c^2 ≤ 1/(d:ℝ)^2 := by
      rw [le_div_iff₀ hd2_pos]
      nlinarith [hcase]
    linarith
  -- Jordan: cos(π/(2d))² ≤ 1 - 1/d² ≤ c².
  have hjordan := jordan_cos_sq_le d hd1
  have hcsq : Real.cos (Real.pi / (2 * d))^2 ≤ c^2 := le_trans hjordan hc2ge
  -- So cos(π/(2d)) ≤ |cos(π/(2d))| ≤ |c|.
  have hcabs : Real.cos (Real.pi / (2 * d)) ≤ |c| := by
    calc Real.cos (Real.pi / (2 * d)) ≤ |Real.cos (Real.pi / (2 * d))| := le_abs_self _
      _ ≤ |c| := by
          have h1 := Real.sqrt_le_sqrt hcsq
          rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs] at h1
  exact cheb_alt_compare p hd1 hd h c hc1 hc2 hcabs
