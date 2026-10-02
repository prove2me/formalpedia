-- Prove2me | Theorems.Thm_BookSixth_permanent_bm_upper_zero
-- name    : BookSixth.permanent_bm_upper_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T02:00:05.226864+00:00
-- url     : https://prove2.me/theorems/07959043-9cc9-4b35-af84-b38cab32c99d
-- title:
--   Chapter 37 lemma: Bregman-Minc bound for 0x0 matrices
-- statement:
--   Bregman-Minc for $0 \times 0$ matrices, both sides equal to $1$. Degenerate instance of the permanent estimate behind Chapter 37, Theorem 2.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, Bregman-Minc 0x0 instance, p. 266. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.permanent_bm_upper_zero (M : Matrix (Fin 0) (Fin 0) ℝ) (r : Fin 0 → ℕ)
    (h01 : ∀ i j, M i j = 0 ∨ M i j = 1) (hrow : ∀ i, ∑ j, M i j = (r i : ℝ)) :
    Matrix.permanent M ≤ ∏ i, ((r i).factorial : ℝ) ^ ((1 : ℝ) / (r i : ℝ)) := by sorry
