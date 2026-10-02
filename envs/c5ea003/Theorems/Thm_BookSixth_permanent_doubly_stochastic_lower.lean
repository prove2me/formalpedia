-- Prove2me | Theorems.Thm_BookSixth_permanent_doubly_stochastic_lower
-- name    : BookSixth.permanent_doubly_stochastic_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T23:27:44.137717+00:00
-- url     : https://prove2.me/theorems/300f6287-9904-4b40-9143-88d08d60c79e
-- title:
--   Chapter 37 lemma: van der Waerden permanent lower bound
-- statement:
--   Van der Waerden's theorem (Egorychev-Falikman): the permanent of a doubly stochastic $n\times n$ real matrix is at least $n!/n^n$. This is the permanent estimate behind the lower counting bound of Chapter 37, Theorem 2.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, permanent lower bound used for Theorem 2, p. 266. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.permanent_doubly_stochastic_lower (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hnn : ∀ i j, 0 ≤ M i j) (hrow : ∀ i, ∑ j, M i j = 1) (hcol : ∀ j, ∑ i, M i j = 1) :
    (n.factorial : ℝ) / (n : ℝ) ^ n ≤ Matrix.permanent M := by sorry
