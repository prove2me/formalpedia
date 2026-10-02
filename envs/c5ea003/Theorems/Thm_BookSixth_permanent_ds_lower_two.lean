-- Prove2me | Theorems.Thm_BookSixth_permanent_ds_lower_two
-- name    : BookSixth.permanent_ds_lower_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T00:56:33.47556+00:00
-- url     : https://prove2.me/theorems/b6e15976-ce81-462f-a377-2c19cc80236b
-- title:
--   Chapter 37 lemma: van der Waerden bound for 2x2 matrices
-- statement:
--   Van der Waerden's bound for $2 \times 2$ doubly stochastic matrices: the permanent is at least $2!/2^2 = 1/2$. Base instance of the permanent estimate behind Chapter 37, Theorem 2.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, van der Waerden 2x2 instance, p. 266. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.permanent_ds_lower_two (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hnn : ∀ i j, 0 ≤ M i j) (hrow : ∀ i, ∑ j, M i j = 1) (hcol : ∀ j, ∑ i, M i j = 1) :
    ((2 : ℕ).factorial : ℝ) / (2 : ℝ) ^ 2 ≤ Matrix.permanent M := by sorry
