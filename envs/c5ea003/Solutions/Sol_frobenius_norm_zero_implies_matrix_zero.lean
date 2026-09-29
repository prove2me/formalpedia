-- Prove2me | solution 1 for frobenius_norm_zero_implies_matrix_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:08:30.983722+00:00
-- url     : https://prove2.me/submissions/1145b9ca-2404-485e-adac-b23f7a7a170a

import Definitions.Def_matrix_completion_tangent
import Mathlib.Tactic.Linarith

open MatrixCompletion

theorem solution
    {n₁ n₂ : ℕ} (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    frobeniusNorm X = 0 → X = 0 := by
  intro hnorm
  ext i j
  have hsumsq_zero : frobeniusNormSq X = 0 := by
    have hsqrt_sq := congrArg (fun x : ℝ => x ^ 2) hnorm
    have hnonneg : 0 ≤ frobeniusNormSq X := by
      unfold frobeniusNormSq
      positivity
    simpa [frobeniusNorm, Real.sq_sqrt hnonneg] using hsqrt_sq
  have hrow_nonneg : ∀ i : Fin n₁, 0 ≤ ∑ j : Fin n₂, X i j ^ 2 := by
    intro i
    positivity
  have hrow_zero : ∑ j : Fin n₂, X i j ^ 2 = 0 := by
    have hle :
        ∑ j : Fin n₂, X i j ^ 2 ≤ ∑ i : Fin n₁, ∑ j : Fin n₂, X i j ^ 2 := by
      exact Finset.single_le_sum (fun x _ => hrow_nonneg x) (Finset.mem_univ i)
    unfold frobeniusNormSq at hsumsq_zero
    linarith [hrow_nonneg i]
  have hentry_nonneg : ∀ j : Fin n₂, 0 ≤ X i j ^ 2 := by
    intro j
    positivity
  have hentry_zero : X i j ^ 2 = 0 := by
    have hle : X i j ^ 2 ≤ ∑ j : Fin n₂, X i j ^ 2 := by
      exact Finset.single_le_sum (fun x _ => hentry_nonneg x) (Finset.mem_univ j)
    linarith [hentry_nonneg j]
  exact sq_eq_zero_iff.mp hentry_zero
