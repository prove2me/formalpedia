-- Prove2me | Theorems.Thm_BookSixth_permanent_ds_lower_one
-- name    : BookSixth.permanent_ds_lower_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T01:04:42.831957+00:00
-- url     : https://prove2.me/theorems/c76e3d6d-8f9f-4db8-b917-5639fbe0a9a5
-- title:
--   Chapter 37 lemma: van der Waerden bound for 1x1 matrices
-- statement:
--   Van der Waerden's bound for $1 \times 1$ doubly stochastic matrices: the permanent is at least $1!/1^1 = 1$. Base instance of the permanent estimate behind Chapter 37, Theorem 2.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, van der Waerden 1x1 instance, p. 266. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.permanent_ds_lower_one (M : Matrix (Fin 1) (Fin 1) ℝ)
    (hnn : ∀ i j, 0 ≤ M i j) (hrow : ∀ i, ∑ j, M i j = 1) (hcol : ∀ j, ∑ i, M i j = 1) :
    ((1 : ℕ).factorial : ℝ) / (1 : ℝ) ^ 1 ≤ Matrix.permanent M := by sorry
