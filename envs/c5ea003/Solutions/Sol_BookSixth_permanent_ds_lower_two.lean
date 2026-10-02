-- Prove2me | solution 1 for BookSixth.permanent_ds_lower_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T00:57:00.498716+00:00
-- url     : https://prove2.me/submissions/ef28719a-f1e7-4472-ad78-852961d842f2

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hnn : ∀ i j, 0 ≤ M i j)
    (hrow : ∀ i, ∑ j, M i j = 1) (hcol : ∀ j, ∑ i, M i j = 1) :
    ((2 : ℕ).factorial : ℝ) / (2 : ℝ) ^ 2 ≤ Matrix.permanent M := by
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by
    decide
  have h1s : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by decide
  have hperm : Matrix.permanent M = M 0 0 * M 1 1 + M 1 0 * M 0 1 := by
    rw [Matrix.permanent, huniv, Finset.sum_pair h1s]
    congr 1
    · simp [Fin.prod_univ_two]
    · simp [Fin.prod_univ_two]
  have r0 := hrow 0
  have r1 := hrow 1
  have c0 := hcol 0
  rw [Fin.sum_univ_two] at r0 r1 c0
  rw [hperm]
  norm_num [Nat.factorial_two]
  nlinarith [hnn 0 0, hnn 0 1, hnn 1 0, hnn 1 1, r0, r1, c0,
    sq_nonneg (M 0 0 - 1 / 2)]
