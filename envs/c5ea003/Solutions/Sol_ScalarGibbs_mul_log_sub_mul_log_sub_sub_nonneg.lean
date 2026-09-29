-- Prove2me | solution 1 for ScalarGibbs.mul_log_sub_mul_log_sub_sub_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-23T03:25:44.487053+00:00
-- url     : https://prove2.me/submissions/f731740f-a3b1-404d-bea4-966517c2aac6

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Exp
open Real

theorem solution {y u : ℝ} (hy : 0 ≤ y) (hu : 0 < u) :
    0 ≤ y * Real.log y - y * Real.log u - (y - u) := by
  rcases eq_or_lt_of_le hy with hy0 | hy0
  · subst hy0; simp; exact hu.le
  · have hdual0 : 1 - (y / u)⁻¹ ≤ Real.log (y / u) :=
      Real.one_sub_inv_le_log_of_pos (by positivity)
    rw [Real.log_div (ne_of_gt hy0) (ne_of_gt hu)] at hdual0
    have hinv : (y / u)⁻¹ = u / y := by rw [inv_div]
    rw [hinv] at hdual0
    have hmul : y * (1 - u / y) ≤ y * (Real.log y - Real.log u) :=
      mul_le_mul_of_nonneg_left hdual0 hy0.le
    have heq : y * (1 - u / y) = y - u := by field_simp
    rw [heq] at hmul
    nlinarith [hmul]
