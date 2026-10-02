-- Prove2me | solution 1 for BookSixth.permanent_bm_upper_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T02:00:38.587535+00:00
-- url     : https://prove2.me/submissions/24670b7a-84e9-4af6-b038-6a7d0a3fc5fb

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (M : Matrix (Fin 0) (Fin 0) ℝ) (r : Fin 0 → ℕ)
    (h01 : ∀ i j, M i j = 0 ∨ M i j = 1) (hrow : ∀ i, ∑ j, M i j = (r i : ℝ)) :
    Matrix.permanent M ≤ ∏ i, ((r i).factorial : ℝ) ^ ((1 : ℝ) / (r i : ℝ)) := by
  rw [Matrix.permanent_isEmpty]
  simp
