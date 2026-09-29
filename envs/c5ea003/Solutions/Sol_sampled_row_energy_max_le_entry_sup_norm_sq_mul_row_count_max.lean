-- Prove2me | solution 1 for sampled_row_energy_max_le_entry_sup_norm_sq_mul_row_count_max
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:08:37.028724+00:00
-- url     : https://prove2.me/submissions/7b845381-da1f-41b2-b637-eea8d8fd62f1

import Definitions.Def_matrix_completion_sampled_counts
import Mathlib.Tactic.Positivity

open MatrixCompletion

theorem solution :
    ∀ {n₁ n₂ : ℕ}
      (Omega : Finset (Fin n₁ × Fin n₂))
      (X : Matrix (Fin n₁) (Fin n₂) ℝ),
      sampledRowEnergyMax Omega X ≤
        entrySupNorm X ^ 2 * sampledRowCountMax Omega := by
  intro n₁ n₂ Omega X
  by_cases h₁ : IsEmpty (Fin n₁)
  · haveI := h₁
    simp [sampledRowEnergyMax, sampledRowCountMax]
  · by_cases h₂ : IsEmpty (Fin n₂)
    · haveI := h₂
      simp [sampledRowEnergyMax, sampledRowCountMax]
    · have hn₁ : Nonempty (Fin n₁) := not_isEmpty_iff.mp h₁
      have hn₂ : Nonempty (Fin n₂) := not_isEmpty_iff.mp h₂
      have hentry_nonneg : 0 ≤ entrySupNorm X := by
        rcases hn₁ with ⟨i0⟩
        rcases hn₂ with ⟨j0⟩
        exact le_trans (abs_nonneg (X i0 j0))
          (le_trans
            (le_ciSup
              (Finite.bddAbove_range (fun j : Fin n₂ => |X i0 j|)) j0)
            (le_ciSup
              (Finite.bddAbove_range
                (fun i : Fin n₁ => ⨆ j : Fin n₂, |X i j|)) i0))
      unfold sampledRowEnergyMax
      apply ciSup_le
      intro i
      unfold sampledRowCountMax
      have hrow :
          (∑ j : Fin n₂, if (i, j) ∈ Omega then X i j ^ 2 else 0) ≤
            entrySupNorm X ^ 2 *
              (∑ j : Fin n₂, if (i, j) ∈ Omega then (1 : ℝ) else 0) := by
        calc
          (∑ j : Fin n₂, if (i, j) ∈ Omega then X i j ^ 2 else 0)
              ≤ ∑ j : Fin n₂,
                  if (i, j) ∈ Omega then entrySupNorm X ^ 2 else 0 := by
                apply Finset.sum_le_sum
                intro j _hj
                by_cases hmem : (i, j) ∈ Omega
                · simp [hmem]
                  have hij_abs : |X i j| ≤ entrySupNorm X := by
                    exact le_trans
                      (le_ciSup
                        (Finite.bddAbove_range
                          (fun j : Fin n₂ => |X i j|)) j)
                      (le_ciSup
                        (Finite.bddAbove_range
                          (fun i : Fin n₁ => ⨆ j : Fin n₂, |X i j|)) i)
                  rw [← sq_abs (X i j)]
                  exact sq_le_sq'
                    (le_trans (neg_nonpos.mpr hentry_nonneg) (abs_nonneg (X i j)))
                    hij_abs
                · simp [hmem]
          _ = entrySupNorm X ^ 2 *
              (∑ j : Fin n₂, if (i, j) ∈ Omega then (1 : ℝ) else 0) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j _hj
                by_cases hmem : (i, j) ∈ Omega
                · simp [hmem]
                · simp [hmem]
      exact le_trans hrow
        (mul_le_mul_of_nonneg_left
          (le_ciSup
            (Finite.bddAbove_range
              (fun i : Fin n₁ =>
                ∑ j : Fin n₂, if (i, j) ∈ Omega then (1 : ℝ) else 0)) i)
          (sq_nonneg (entrySupNorm X)))
