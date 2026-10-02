-- Prove2me | Theorems.Thm_BookSixth_permanent_bm_upper_two
-- name    : BookSixth.permanent_bm_upper_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T01:11:03.456892+00:00
-- url     : https://prove2.me/theorems/cf3d2234-fa3d-4566-9d51-fded95256d53
-- title:
--   Chapter 37 lemma: Bregman-Minc bound for 2x2 matrices
-- statement:
--   Bregman-Minc for $2 \times 2$ 0-1 matrices: the permanent is at most $(r_0!)^{1/r_0}(r_1!)^{1/r_1}$ where $r_i$ are the row sums. Instance of the permanent estimate behind the upper counting bound of Chapter 37, Theorem 2.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, Bregman-Minc 2x2 instance, p. 266. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.permanent_bm_upper_two (M : Matrix (Fin 2) (Fin 2) ℝ) (r : Fin 2 → ℕ)
    (h01 : ∀ i j, M i j = 0 ∨ M i j = 1) (hrow : ∀ i, ∑ j, M i j = (r i : ℝ)) :
    Matrix.permanent M ≤ ∏ i, ((r i).factorial : ℝ) ^ ((1 : ℝ) / (r i : ℝ)) := by sorry
