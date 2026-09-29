-- Prove2me | solution 1 for sampled_row_count_max_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:08:36.762079+00:00
-- url     : https://prove2.me/submissions/b7736a4d-e260-4576-b075-08eb0a8686aa

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
