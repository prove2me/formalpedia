-- Prove2me | solution 1 for BookSixth.permanent_mono_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T00:34:37.477702+00:00
-- url     : https://prove2.me/submissions/b8c4d7a1-af90-4111-8336-cfbb36c60394

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ)
    (hnn : ∀ i j, 0 ≤ A i j) (hle : ∀ i j, A i j ≤ B i j) :
    Matrix.permanent A ≤ Matrix.permanent B := by
  unfold Matrix.permanent
  apply Finset.sum_le_sum
  intro σ _
  apply Finset.prod_le_prod
  · intro i _
    exact hnn _ _
  · intro i _
    exact hle _ _
