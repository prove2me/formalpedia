-- Prove2me | solution 1 for entry_sup_norm_tangent_diagonal_multiplier_bound_from_kernel_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T14:26:53.416131+00:00
-- url     : https://prove2.me/submissions/5353a54b-22c5-4575-bd52-bcc88204e944

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

private lemma abs_entry_le_entrySupNorm {n₁ n₂ : ℕ}
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (i : Fin n₁) (j : Fin n₂) :
    |X i j| ≤ entrySupNorm X := by
  unfold entrySupNorm
  exact Finite.le_ciSup_of_le i (Finite.le_ciSup_of_le j le_rfl)

/-- A pointwise diagonal-kernel bound controls the entry-sup norm of the
tangent diagonal multiplier. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (S : SVD M r) (X : Matrix (Fin n₁) (Fin n₂) ℝ) {a : ℝ} :
    0 ≤ a →
    (∀ i j, |tangentCoordinateKernel S i j i j| ≤ a) →
    entrySupNorm (tangentDiagonalMultiplier S X) ≤ a * entrySupNorm X := by
  intro _ha hk
  apply entrySupNorm_le_of_forall_abs_le hn₁ hn₂
  intro i j
  unfold tangentDiagonalMultiplier
  calc
    |X i j * tangentCoordinateKernel S i j i j|
        = |X i j| * |tangentCoordinateKernel S i j i j| := by
          rw [abs_mul]
    _ ≤ entrySupNorm X * a :=
          mul_le_mul (abs_entry_le_entrySupNorm X i j) (hk i j)
            (abs_nonneg _) (le_trans (abs_nonneg _) (abs_entry_le_entrySupNorm X i j))
    _ = a * entrySupNorm X := by ring
