-- Prove2me | solution 1 for BookSixth.permanent_zero_one_le_factorial
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T00:40:33.146976+00:00
-- url     : https://prove2.me/submissions/d9a0aca8-862c-40a5-ac87-c02990a30d73

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ)
    (h01 : ∀ i j, M i j = 0 ∨ M i j = 1) :
    Matrix.permanent M ≤ (n.factorial : ℝ) := by
  unfold Matrix.permanent
  calc ∑ σ : Equiv.Perm (Fin n), ∏ i, M (σ i) i
      ≤ ∑ _σ : Equiv.Perm (Fin n), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro σ _
        have hle : ∏ i, M (σ i) i ≤ ∏ _i : Fin n, (1 : ℝ) := by
          apply Finset.prod_le_prod
          · intro i _
            rcases h01 _ _ with h | h <;> rw [h] <;> norm_num
          · intro i _
            rcases h01 _ _ with h | h <;> rw [h] <;> norm_num
        simpa using hle
    _ = (n.factorial : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one,
          Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
