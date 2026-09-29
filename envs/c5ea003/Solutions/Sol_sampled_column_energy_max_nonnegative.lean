-- Prove2me | solution 1 for sampled_column_energy_max_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:08:36.518885+00:00
-- url     : https://prove2.me/submissions/01489bb3-ea1f-496f-82ee-ee732365f34e

import Definitions.Def_matrix_completion_sampled_counts
import Mathlib.Tactic.Positivity

open MatrixCompletion

theorem solution :
    ∀ {n₁ n₂ : ℕ} (Omega : Finset (Fin n₁ × Fin n₂))
      (X : Matrix (Fin n₁) (Fin n₂) ℝ),
      0 ≤ sampledColumnEnergyMax Omega X := by
  intro n₁ n₂ Omega X
  unfold sampledColumnEnergyMax
  by_cases h : IsEmpty (Fin n₂)
  · haveI := h
    simp
  · have hn : Nonempty (Fin n₂) := not_isEmpty_iff.mp h
    rcases hn with ⟨j⟩
    exact le_trans
      (by
        positivity :
          (0 : ℝ) ≤ ∑ i : Fin n₁, if (i, j) ∈ Omega then X i j ^ 2 else 0)
      (le_ciSup
        (Finite.bddAbove_range
          (fun j : Fin n₂ =>
            ∑ i : Fin n₁, if (i, j) ∈ Omega then X i j ^ 2 else 0)) j)
