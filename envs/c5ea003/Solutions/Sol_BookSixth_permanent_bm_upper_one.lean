-- Prove2me | solution 1 for BookSixth.permanent_bm_upper_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T01:01:56.97317+00:00
-- url     : https://prove2.me/submissions/7c6fa471-2d48-455a-b653-aa3a87c2d25b

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (M : Matrix (Fin 1) (Fin 1) ℝ) (r : Fin 1 → ℕ)
    (h01 : ∀ i j, M i j = 0 ∨ M i j = 1) (hrow : ∀ i, ∑ j, M i j = (r i : ℝ)) :
    Matrix.permanent M ≤ ∏ i, ((r i).factorial : ℝ) ^ ((1 : ℝ) / (r i : ℝ)) := by
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 1))) = {1} := by decide
  have hperm : Matrix.permanent M = M 0 0 := by
    rw [Matrix.permanent, huniv, Finset.sum_singleton, Fin.prod_univ_one]
    simp
  have hr : M 0 0 = (r 0 : ℝ) := by
    have h := hrow 0
    rw [Fin.sum_univ_one] at h
    exact h
  rw [hperm, Fin.prod_univ_one]
  rcases h01 0 0 with h | h
  · rw [h] at hr
    have hr0 : r 0 = 0 := by exact_mod_cast hr.symm
    rw [hr0, h]
    norm_num
  · rw [h] at hr
    have hr0 : r 0 = 1 := by exact_mod_cast hr.symm
    rw [hr0, h]
    norm_num
