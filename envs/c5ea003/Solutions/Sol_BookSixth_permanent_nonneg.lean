-- Prove2me | solution 1 for BookSixth.permanent_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T00:37:35.010757+00:00
-- url     : https://prove2.me/submissions/c130f9e7-8bfb-4501-b65f-8a6f2da43848

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ)
    (hnn : ∀ i j, 0 ≤ M i j) :
    0 ≤ Matrix.permanent M := by
  unfold Matrix.permanent
  apply Finset.sum_nonneg
  intro σ _
  apply Finset.prod_nonneg
  intro i _
  exact hnn _ _
