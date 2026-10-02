-- Prove2me | Theorems.Thm_BookSixth_permanent_bm_upper_one
-- name    : BookSixth.permanent_bm_upper_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T00:59:35.631686+00:00
-- url     : https://prove2.me/theorems/0ba2945f-3af5-4554-a5eb-1e32a15804e4
-- title:
--   Chapter 37 lemma: Bregman-Minc bound for 1x1 matrices
-- statement:
--   Bregman-Minc for $1 \times 1$ 0-1 matrices: the permanent is at most $(r_0!)^{1/r_0}$ where $r_0$ is the row sum. Base instance of the permanent estimate behind the upper counting bound of Chapter 37, Theorem 2.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, Bregman-Minc 1x1 instance, p. 266. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.permanent_bm_upper_one (M : Matrix (Fin 1) (Fin 1) ℝ) (r : Fin 1 → ℕ)
    (h01 : ∀ i j, M i j = 0 ∨ M i j = 1) (hrow : ∀ i, ∑ j, M i j = (r i : ℝ)) :
    Matrix.permanent M ≤ ∏ i, ((r i).factorial : ℝ) ^ ((1 : ℝ) / (r i : ℝ)) := by sorry
