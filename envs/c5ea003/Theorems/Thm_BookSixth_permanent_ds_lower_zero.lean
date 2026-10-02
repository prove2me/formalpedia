-- Prove2me | Theorems.Thm_BookSixth_permanent_ds_lower_zero
-- name    : BookSixth.permanent_ds_lower_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T02:00:02.81119+00:00
-- url     : https://prove2.me/theorems/ae718d10-0a9b-4751-b70c-df3b49ed940c
-- title:
--   Chapter 37 lemma: van der Waerden bound for 0x0 matrices
-- statement:
--   Van der Waerden's bound for $0 \times 0$ matrices, both sides equal to $1$. Degenerate instance of the permanent estimate behind Chapter 37, Theorem 2.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, van der Waerden 0x0 instance, p. 266. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.permanent_ds_lower_zero (M : Matrix (Fin 0) (Fin 0) ℝ)
    (hnn : ∀ i j, 0 ≤ M i j) (hrow : ∀ i, ∑ j, M i j = 1) (hcol : ∀ j, ∑ i, M i j = 1) :
    ((0 : ℕ).factorial : ℝ) / (0 : ℝ) ^ 0 ≤ Matrix.permanent M := by sorry
