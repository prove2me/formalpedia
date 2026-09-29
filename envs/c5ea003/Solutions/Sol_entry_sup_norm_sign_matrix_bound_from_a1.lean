-- Prove2me | solution 1 for entry_sup_norm_sign_matrix_bound_from_a1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T14:37:16.446333+00:00
-- url     : https://prove2.me/submissions/481346e0-448b-40a5-8e56-53aad0c60c63

import Mathlib.Data.Fintype.Order
import Definitions.Def_matrix_completion_neumann

open MatrixCompletion
open scoped Classical BigOperators

private lemma entrySupNorm_le_of_forall_abs_le {n₁ n₂ : ℕ}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (B : ℝ)
    (h : ∀ i j, |X i j| ≤ B) :
    entrySupNorm X ≤ B := by
  haveI : Nonempty (Fin n₁) := Fin.pos_iff_nonempty.mp hn₁
  haveI : Nonempty (Fin n₂) := Fin.pos_iff_nonempty.mp hn₂
  unfold entrySupNorm
  exact ciSup_le fun i => ciSup_le fun j => h i j

/-- The A1 incoherence assumption gives the entry-sup norm bound for the sign
matrix. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (μ₁ : ℝ) (S : SVD M r) :
    A1 S μ₁ →
    entrySupNorm (signMatrix S) ≤
      μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
  intro hA1
  exact entrySupNorm_le_of_forall_abs_le hn₁ hn₂ (signMatrix S) _ hA1
