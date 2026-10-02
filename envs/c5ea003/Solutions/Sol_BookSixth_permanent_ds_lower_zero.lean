-- Prove2me | solution 1 for BookSixth.permanent_ds_lower_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T02:00:54.003881+00:00
-- url     : https://prove2.me/submissions/179c1dd8-2177-43a2-87ef-54bee0969551

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (M : Matrix (Fin 0) (Fin 0) ℝ)
    (hnn : ∀ i j, 0 ≤ M i j)
    (hrow : ∀ i, ∑ j, M i j = 1) (hcol : ∀ j, ∑ i, M i j = 1) :
    ((0 : ℕ).factorial : ℝ) / (0 : ℝ) ^ 0 ≤ Matrix.permanent M := by
  rw [Matrix.permanent_isEmpty]
  norm_num
