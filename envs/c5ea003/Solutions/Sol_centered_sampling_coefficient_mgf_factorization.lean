-- Prove2me | solution 1 for centered_sampling_coefficient_mgf_factorization
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T23:54:54.143747+00:00
-- url     : https://prove2.me/submissions/698ce4b6-b11c-4116-b7f6-5c3e85c0878a

import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_bernoulli_powerset_expectation_prod_factor
import Mathlib.Analysis.SpecialFunctions.Exp

open MatrixCompletion
open scoped BigOperators Classical

/-- Reduction of the MGF factorization onto the Proved independence/product
factorization `bernoulli_powerset_expectation_prod_factor`. -/
theorem solution {n₁ n₂ : ℕ}
    (p : ℝ) (B : Matrix (Fin n₁) (Fin n₂) ℝ) (lam : ℝ) :
    bernoulliExpectation p
        (fun Omega =>
          Real.exp (lam * matrixEntrySum (centeredSamplingFluctuation Omega p B))) =
      ∏ w : Fin n₁ × Fin n₂,
        (p * Real.exp (lam * (p⁻¹ * (B w.1 w.2) * (1 - p)))
          + (1 - p) * Real.exp (lam * (p⁻¹ * (B w.1 w.2) * (0 - p)))) := by
  classical
  set f : (Fin n₁ × Fin n₂) → ℝ → ℝ :=
    fun w x => Real.exp (lam * (p⁻¹ * (B w.1 w.2) * (x - p))) with hf
  have key := bernoulli_powerset_expectation_prod_factor (n₁ := n₁) (n₂ := n₂) p f
  have hL : (fun Omega : Finset (Fin n₁ × Fin n₂) =>
        ∏ w : Fin n₁ × Fin n₂, f w (if w ∈ Omega then 1 else 0)) =
      (fun Omega =>
        Real.exp (lam * matrixEntrySum (centeredSamplingFluctuation Omega p B))) := by
    funext Omega
    have hcoeff : matrixEntrySum (centeredSamplingFluctuation Omega p B) =
        ∑ w : Fin n₁ × Fin n₂,
          (p⁻¹ * (B w.1 w.2) * ((if w ∈ Omega then 1 else 0) - p)) := by
      unfold matrixEntrySum centeredSamplingFluctuation samplingProjection
      apply Finset.sum_congr rfl
      intro w _
      simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
      by_cases h : (w.1, w.2) ∈ Omega
      · simp only [h, if_true]; ring
      · simp only [h, if_false]; ring
    rw [hcoeff, Finset.mul_sum, Real.exp_sum]
  rw [hL] at key
  rw [key]
