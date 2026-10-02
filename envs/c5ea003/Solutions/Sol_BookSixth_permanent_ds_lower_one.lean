-- Prove2me | solution 1 for BookSixth.permanent_ds_lower_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T01:05:08.765338+00:00
-- url     : https://prove2.me/submissions/dbe5115f-dddd-4d3f-b7cf-da1204bec81a

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (M : Matrix (Fin 1) (Fin 1) ℝ)
    (hnn : ∀ i j, 0 ≤ M i j)
    (hrow : ∀ i, ∑ j, M i j = 1) (hcol : ∀ j, ∑ i, M i j = 1) :
    ((1 : ℕ).factorial : ℝ) / (1 : ℝ) ^ 1 ≤ Matrix.permanent M := by
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 1))) = {1} := by decide
  have hperm : Matrix.permanent M = M 0 0 := by
    rw [Matrix.permanent, huniv, Finset.sum_singleton, Fin.prod_univ_one]
    simp
  have hr : M 0 0 = 1 := by
    have h := hrow 0
    rw [Fin.sum_univ_one] at h
    exact h
  rw [hperm, hr]
  norm_num
