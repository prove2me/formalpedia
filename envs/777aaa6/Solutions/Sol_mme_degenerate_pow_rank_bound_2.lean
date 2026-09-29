-- Prove2me | solution 2 for mme_degenerate_pow_rank_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T08:56:56.914272+00:00
-- url     : https://prove2.me/submissions/dd82bb48-8d81-4c21-913d-63204e2bb2f5

import Theorems.Thm_mme_kronPow_degenerate
import Theorems.Thm_mme_degenerate_rank_le
import Theorems.Thm_mme_poly_root_tendsto_one

open MME Filter Topology

universe u

/-- A finite-order degeneration gives polynomial overhead in the ranks of tensor powers. -/
theorem solution {K : Type u} [Field K] {d : ℕ}
    {X : TensorObj K d} {r : ℕ} (h : Degenerates X (TensorObj.diagObj K d r)) :
    ∃ C : ℕ → ℝ, (∀ n, (1 : ℝ) ≤ C n) ∧
      Filter.Tendsto (fun n => (C (n + 1)) ^ ((1 : ℝ) / (n + 1))) Filter.atTop (nhds 1) ∧
      ∀ n, (tensorRankObj (TensorObj.kronPow X (n + 1)) : ℝ) ≤ (r : ℝ) ^ (n + 1) * C (n + 1) := by
  obtain ⟨hh, hdeg⟩ := h
  refine ⟨fun m => (((m * hh + 1) ^ d : ℕ) : ℝ), ?_, ?_, ?_⟩
  · intro n
    show (1 : ℝ) ≤ (((n * hh + 1) ^ d : ℕ) : ℝ)
    exact_mod_cast Nat.one_le_pow d (n * hh + 1) (by omega)
  · exact mme_poly_root_tendsto_one hh d
  · intro n
    have h2 := _root_.mme_degenerate_rank_le (_root_.mme_kronPow_degenerate hdeg (n + 1))
    calc (tensorRankObj (TensorObj.kronPow X (n + 1)) : ℝ)
        ≤ ((r ^ (n + 1) * ((n + 1) * hh + 1) ^ d : ℕ) : ℝ) := by exact_mod_cast h2
      _ = (r : ℝ) ^ (n + 1) * ((((n + 1) * hh + 1) ^ d : ℕ) : ℝ) := by push_cast; ring


#print axioms solution
