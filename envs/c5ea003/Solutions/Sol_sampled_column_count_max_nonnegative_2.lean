-- Prove2me | solution 2 for sampled_column_count_max_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:11:20.272423+00:00
-- url     : https://prove2.me/submissions/f6d6ae06-5b39-43e3-baff-1f29879ebbf2

import Definitions.Def_matrix_completion_sampled_counts
import Mathlib.Tactic.Positivity

open MatrixCompletion

theorem solution :
    ∀ {n₁ n₂ : ℕ} (Omega : Finset (Fin n₁ × Fin n₂)),
      0 ≤ sampledColumnCountMax Omega := by
  intro n₁ n₂ Omega
  unfold sampledColumnCountMax
  by_cases h : IsEmpty (Fin n₂)
  · haveI := h
    simp
  · have hn : Nonempty (Fin n₂) := not_isEmpty_iff.mp h
    rcases hn with ⟨j⟩
    exact le_trans
      (by
        positivity :
          (0 : ℝ) ≤ ∑ i : Fin n₁, if (i, j) ∈ Omega then (1 : ℝ) else 0)
      (le_ciSup
        (Finite.bddAbove_range
          (fun j : Fin n₂ =>
            ∑ i : Fin n₁, if (i, j) ∈ Omega then (1 : ℝ) else 0)) j)
