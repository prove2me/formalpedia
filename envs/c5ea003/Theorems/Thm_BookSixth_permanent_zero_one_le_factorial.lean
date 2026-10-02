-- Prove2me | Theorems.Thm_BookSixth_permanent_zero_one_le_factorial
-- name    : BookSixth.permanent_zero_one_le_factorial
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T00:40:12.899626+00:00
-- url     : https://prove2.me/theorems/9bb05f1f-7404-4609-a0b6-1389ea7768f8
-- title:
--   Chapter 37 adapter: 0-1 permanent bounded by factorial
-- statement:
--   The permanent of an $n \times n$ 0-1 real matrix is at most $n!$: a crude corollary on the road to the Bregman-Minc bound behind Chapter 37, Theorem 2.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, 0-1 permanent crude bound adapter, p. 266. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.permanent_zero_one_le_factorial (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ)
    (h01 : ∀ i j, M i j = 0 ∨ M i j = 1) :
    Matrix.permanent M ≤ (n.factorial : ℝ) := by sorry
