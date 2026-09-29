-- Prove2me | solution 1 for OracleTeam.ensemble_no_worse_than_best
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T16:54:05.401433+00:00
-- url     : https://prove2.me/submissions/ba8d5999-1fd5-4454-b154-0e1f3d9c9e96

-- Sol generated from Evergreen/Prediction/OracleTeam.lean
import Mathlib
import Definitions.Def_Evergreen_Prediction_OracleTeam
/-
  # The Oracle Team: Collaborative Prediction Architecture
-/


open Finset BigOperators

open OracleTeam

/-! ## Section 1: Oracle Types -/


/-! ## Section 2: The Oracle Council -/




/-! ## Section 3: Ensemble Error Bound -/


/-! ## Section 4: Prediction Hedging -/




open OracleTeam in
theorem solution{n : ℕ}
    (predictions : Fin n → ℝ) (truth : ℝ)
    (weights : Fin n → ℝ) (hw_nn : ∀ i, 0 ≤ weights i)
    (hw_sum : ∑ i, weights i = 1) :
    let ensemble := ∑ i, weights i * predictions i
    |ensemble - truth| ≤ ∑ i, weights i * |predictions i - truth| := by
  simp only
  calc |∑ i, weights i * predictions i - truth|
      = |∑ i, weights i * predictions i - (∑ i, weights i) * truth| := by
        rw [hw_sum, one_mul]
    _ = |∑ i, (weights i * predictions i - weights i * truth)| := by
        congr 1; rw [Finset.sum_sub_distrib]; congr 1; rw [Finset.sum_mul]
    _ = |∑ i, weights i * (predictions i - truth)| := by
        congr 1; congr 1; ext i; ring
    _ ≤ ∑ i, |weights i * (predictions i - truth)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, weights i * |predictions i - truth| := by
        congr 1; ext i; rw [abs_mul, abs_of_nonneg (hw_nn i)]
