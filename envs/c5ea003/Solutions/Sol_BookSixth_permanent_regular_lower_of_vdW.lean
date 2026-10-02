-- Prove2me | solution 1 for BookSixth.permanent_regular_lower_of_vdW
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T01:45:26.265945+00:00
-- url     : https://prove2.me/submissions/204ba450-508d-490c-a873-df13ecbeccc6

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (n : ℕ) (hn : 0 < n)
    (M : Matrix (Fin n) (Fin n) ℝ) (d : ℕ)
    (h01 : ∀ i j, M i j = 0 ∨ M i j = 1)
    (hrow : ∀ i, ∑ j, M i j = (d : ℝ)) (hcol : ∀ j, ∑ i, M i j = (d : ℝ))
    (hvdW : ∀ (A : Matrix (Fin n) (Fin n) ℝ),
      (∀ i j, 0 ≤ A i j) → (∀ i, ∑ j, A i j = 1) → (∀ j, ∑ i, A i j = 1) →
      (n.factorial : ℝ) / (n : ℝ) ^ n ≤ Matrix.permanent A) :
    (d : ℝ) ^ n * ((n.factorial : ℝ) / (n : ℝ) ^ n) ≤ Matrix.permanent M := by
  have hnn : ∀ i j, 0 ≤ M i j := by
    intro i j
    rcases h01 i j with h | h <;> rw [h] <;> norm_num
  have hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · -- degenerate case: all entries vanish, both sides are zero
    subst hd0
    have hzero : M = 0 := by
      ext i j
      simp only [Matrix.zero_apply]
      have hle : M i j ≤ ∑ k, M i k :=
        Finset.single_le_sum (fun k _ => hnn i k) (Finset.mem_univ j)
      have hs := hrow i
      norm_num at hs
      linarith [hnn i j]
    rw [hzero, Matrix.permanent_zero]
    norm_num [hn.ne']
  · -- scale to a doubly stochastic matrix and apply van der Waerden
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hdpos.ne'
    set N : Matrix (Fin n) (Fin n) ℝ := (d : ℝ)⁻¹ • M with hN
    have hM : M = (d : ℝ) • N := by
      rw [hN, smul_smul, mul_inv_cancel₀ hdR, one_smul]
    have hNnn : ∀ i j, 0 ≤ N i j := by
      intro i j
      rw [hN]
      simp only [Matrix.smul_apply, smul_eq_mul]
      apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (hnn i j)
    have hNrow : ∀ i, ∑ j, N i j = 1 := by
      intro i
      rw [hN]
      simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, hrow i]
      exact inv_mul_cancel₀ hdR
    have hNcol : ∀ j, ∑ i, N i j = 1 := by
      intro j
      rw [hN]
      simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, hcol j]
      exact inv_mul_cancel₀ hdR
    rw [hM, Matrix.permanent_smul, Fintype.card_fin]
    exact mul_le_mul_of_nonneg_left (hvdW N hNnn hNrow hNcol) (pow_nonneg (Nat.cast_nonneg _) _)
