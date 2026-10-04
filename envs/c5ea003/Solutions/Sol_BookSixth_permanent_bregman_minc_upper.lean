-- Prove2me | solution 1 for BookSixth.permanent_bregman_minc_upper
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-09-22T07:01:38.759633+00:00
-- url     : https://prove2.me/submissions/2573328e-0532-4d22-b34c-341908d8f3c2

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_bregman_minc
open scoped BigOperators
open BookSixth

noncomputable section

theorem solution (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (r : Fin n → ℕ)
    (h01 : ∀ i j, M i j = 0 ∨ M i j = 1)
    (hrow : ∀ i, ∑ j, M i j = (r i : ℝ)) :
    Matrix.permanent M ≤ ∏ i, ((r i).factorial : ℝ) ^ ((1 : ℝ) / (r i : ℝ)) := by
  classical
  let A : Matrix (Fin n) (Fin n) ℕ := fun i j => if M i j = 1 then 1 else 0
  have hAM : ∀ i j, (A i j : ℝ) = M i j := by
    intro i j
    rcases h01 i j with hij | hij
    · simp [A, hij]
    · simp [A, hij]
  have hA : ∀ i j, A i j ≤ 1 := by
    intro i j
    dsimp [A]
    split <;> omega
  have hsum : ∀ i, ∑ j, A i j = r i := by
    intro i
    apply Nat.cast_injective (R := ℝ)
    rw [Nat.cast_sum]
    simpa only [hAM] using hrow i
  have hperm : Matrix.permanent M = (BookSixth.permanent A : ℝ) := by
    rw [← Matrix.permanent_transpose M]
    simp only [Matrix.permanent, Matrix.transpose_apply, BookSixth.permanent,
      Nat.cast_sum, Nat.cast_prod]
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.prod_congr rfl
    intro i _
    exact (hAM i (σ i)).symm
  by_cases hz : ∃ i, r i = 0
  · obtain ⟨i, hi⟩ := hz
    have hrowzero : ∀ j, A i j = 0 := by
      intro j
      have hle : A i j ≤ ∑ k, A i k :=
        Finset.single_le_sum (fun k _ => Nat.zero_le (A i k)) (Finset.mem_univ j)
      rw [hsum i, hi] at hle
      omega
    have hpermzero : BookSixth.permanent A = 0 := by
      simp only [BookSixth.permanent]
      apply Finset.sum_eq_zero
      intro σ _
      exact Finset.prod_eq_zero (Finset.mem_univ i) (hrowzero (σ i))
    rw [hperm, hpermzero, Nat.cast_zero]
    positivity
  · have hrows : ∀ i, 0 < ∑ j, A i j := by
      intro i
      rw [hsum i]
      have hne : r i ≠ 0 := fun hi => hz ⟨i, hi⟩
      omega
    rw [hperm]
    simpa only [hsum] using BookSixth.bregman_minc A hA hrows

end
