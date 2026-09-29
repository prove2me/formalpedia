-- Prove2me | solution 2 for sampled_row_count_max_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:11:19.978332+00:00
-- url     : https://prove2.me/submissions/87d84645-4daf-4359-98ac-36d5df1093c8

import Definitions.Def_matrix_completion_sampled_counts
import Mathlib.Tactic.Positivity

open MatrixCompletion

theorem solution :
    ∀ {n₁ n₂ : ℕ} (Omega : Finset (Fin n₁ × Fin n₂)),
      0 ≤ sampledRowCountMax Omega := by
  intro n₁ n₂ Omega
  unfold sampledRowCountMax
  by_cases h : IsEmpty (Fin n₁)
  · haveI := h
    simp
  · have hn : Nonempty (Fin n₁) := not_isEmpty_iff.mp h
    rcases hn with ⟨i⟩
    exact le_trans
      (by
        positivity :
          (0 : ℝ) ≤ ∑ j : Fin n₂, if (i, j) ∈ Omega then (1 : ℝ) else 0)
      (le_ciSup
        (Finite.bddAbove_range
          (fun i : Fin n₁ =>
            ∑ j : Fin n₂, if (i, j) ∈ Omega then (1 : ℝ) else 0)) i)
