-- Prove2me | solution 1 for BookSixth.permanent_bm_upper_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T01:17:36.609449+00:00
-- url     : https://prove2.me/submissions/2fbcca0d-7741-4e19-a267-5ccb053eaf6c

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (M : Matrix (Fin 2) (Fin 2) ℝ) (r : Fin 2 → ℕ)
    (h01 : ∀ i j, M i j = 0 ∨ M i j = 1) (hrow : ∀ i, ∑ j, M i j = (r i : ℝ)) :
    Matrix.permanent M ≤ ∏ i, ((r i).factorial : ℝ) ^ ((1 : ℝ) / (r i : ℝ)) := by
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by
    decide
  have h1s : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by decide
  have hperm : Matrix.permanent M = M 0 0 * M 1 1 + M 1 0 * M 0 1 := by
    rw [Matrix.permanent, huniv, Finset.sum_pair h1s]
    congr 1
    · simp [Fin.prod_univ_two]
    · simp [Fin.prod_univ_two]
  have le1 : ∀ i j, M i j ≤ 1 := by
    intro i j
    rcases h01 i j with h | h <;> rw [h] <;> norm_num
  have nn : ∀ i j, 0 ≤ M i j := by
    intro i j
    rcases h01 i j with h | h <;> rw [h] <;> norm_num
  have s0 := hrow 0
  have s1 := hrow 1
  rw [Fin.sum_univ_two] at s0 s1
  have b0 : r 0 ≤ 2 := by
    have h2 : (r 0 : ℝ) ≤ 2 := by linarith [le1 0 0, le1 0 1]
    exact_mod_cast h2
  have b1 : r 1 ≤ 2 := by
    have h2 : (r 1 : ℝ) ≤ 2 := by linarith [le1 1 0, le1 1 1]
    exact_mod_cast h2
  have g1 : ((1 : ℕ).factorial : ℝ) ^ ((1 : ℝ) / ((1 : ℕ) : ℝ)) = 1 := by
    norm_num [Nat.factorial_one]
  have g2 : ((2 : ℕ).factorial : ℝ) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ)) = (2 : ℝ) ^ ((1 : ℝ) / 2) := by
    norm_num [Nat.factorial_two]
  have hcases : r 0 = 0 ∨ r 0 = 1 ∨ r 0 = 2 := by omega
  have hcases1 : r 1 = 0 ∨ r 1 = 1 ∨ r 1 = 2 := by omega
  rw [hperm, Fin.prod_univ_two]
  rcases hcases with e0 | e0 | e0 <;> rcases hcases1 with e1 | e1 | e1
  · -- row 0 sums to 0: permanent vanishes
    rw [e0] at s0
    norm_num at s0
    have z00 : M 0 0 = 0 := by linarith [nn 0 0, nn 0 1]
    have z01 : M 0 1 = 0 := by linarith [nn 0 0, nn 0 1]
    rw [z00, z01]
    simp
    positivity
  · -- (0, 1): permanent vanishes
    rw [e0] at s0
    norm_num at s0
    have z00 : M 0 0 = 0 := by linarith [nn 0 0, nn 0 1]
    have z01 : M 0 1 = 0 := by linarith [nn 0 0, nn 0 1]
    rw [z00, z01]
    simp
    positivity
  · -- (0, 2): permanent vanishes
    rw [e0] at s0
    norm_num at s0
    have z00 : M 0 0 = 0 := by linarith [nn 0 0, nn 0 1]
    have z01 : M 0 1 = 0 := by linarith [nn 0 0, nn 0 1]
    rw [z00, z01]
    simp
    positivity
  · -- row 1 sums to 0: permanent vanishes
    rw [e1] at s1
    norm_num at s1
    have z10 : M 1 0 = 0 := by linarith [nn 1 0, nn 1 1]
    have z11 : M 1 1 = 0 := by linarith [nn 1 0, nn 1 1]
    rw [z10, z11]
    simp
    positivity
  · -- (1, 1): bound is 1
    rw [e0] at s0
    rw [e1] at s1
    norm_num at s0 s1
    rw [e0, e1, g1]
    nlinarith [nn 0 0, nn 0 1, nn 1 0, nn 1 1, le1 0 0, le1 0 1, le1 1 0, le1 1 1, s0, s1]
  · -- (1, 2): bound is sqrt 2 >= 1
    rw [e0] at s0
    rw [e1] at s1
    norm_num at s0 s1
    rw [e0, e1, g1, g2]
    have hsq : (1 : ℝ) ≤ (2 : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    nlinarith [nn 0 0, nn 0 1, nn 1 0, nn 1 1, le1 0 0, le1 0 1, le1 1 0, le1 1 1, s0, s1, hsq]
  · -- row 1 sums to 0: permanent vanishes
    rw [e1] at s1
    norm_num at s1
    have z10 : M 1 0 = 0 := by linarith [nn 1 0, nn 1 1]
    have z11 : M 1 1 = 0 := by linarith [nn 1 0, nn 1 1]
    rw [z10, z11]
    simp
    positivity
  · -- (2, 1): symmetric
    rw [e0] at s0
    rw [e1] at s1
    norm_num at s0 s1
    rw [e0, e1, g1, g2]
    have hsq : (1 : ℝ) ≤ (2 : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    nlinarith [nn 0 0, nn 0 1, nn 1 0, nn 1 1, le1 0 0, le1 0 1, le1 1 0, le1 1 1, s0, s1, hsq]
  · -- (2, 2): bound is 2
    rw [e0] at s0
    rw [e1] at s1
    norm_num at s0 s1
    rw [e0, e1, g2]
    have hmul : (2 : ℝ) ^ ((1 : ℝ) / 2) * (2 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
      rw [← Real.rpow_add (by norm_num)]
      norm_num
    rw [hmul]
    nlinarith [nn 0 0, nn 0 1, nn 1 0, nn 1 1, le1 0 0, le1 0 1, le1 1 0, le1 1 1, s0, s1]
