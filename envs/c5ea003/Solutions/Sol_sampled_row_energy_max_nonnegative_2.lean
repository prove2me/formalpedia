-- Prove2me | solution 2 for sampled_row_energy_max_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:11:20.504925+00:00
-- url     : https://prove2.me/submissions/a35bd575-2745-4ea3-ba85-4d331f330e67

import Definitions.Def_matrix_completion_sampled_counts
import Mathlib.Tactic.Positivity

open MatrixCompletion

theorem solution :
    ∀ {n₁ n₂ : ℕ} (Omega : Finset (Fin n₁ × Fin n₂))
      (X : Matrix (Fin n₁) (Fin n₂) ℝ),
      0 ≤ sampledRowEnergyMax Omega X := by
  intro n₁ n₂ Omega X
  unfold sampledRowEnergyMax
  by_cases h : IsEmpty (Fin n₁)
  · haveI := h
    simp
  · have hn : Nonempty (Fin n₁) := not_isEmpty_iff.mp h
    rcases hn with ⟨i⟩
    exact le_trans
      (by
        positivity :
          (0 : ℝ) ≤ ∑ j : Fin n₂, if (i, j) ∈ Omega then X i j ^ 2 else 0)
      (le_ciSup
        (Finite.bddAbove_range
          (fun i : Fin n₁ =>
            ∑ j : Fin n₂, if (i, j) ∈ Omega then X i j ^ 2 else 0)) i)
