-- Prove2me | Theorems.Thm_BookSixth_determinant_lower
-- name    : BookSixth.determinant_lower
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-13T01:36:33.907702+00:00
-- url     : https://prove2.me/theorems/ef87faca-88c4-4b3a-9610-7dd3c6bd9fee
-- title:
--   Chapter 7, Theorem 2: strict determinant lower bound
-- statement:
--   For n at least 2 there is a sign matrix with determinant strictly greater than the square root of n!. Boundary clarification: the printed strict statement needs this guard, since for n=1 the maximum determinant is 1.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 7, Theorem 2: strict determinant lower bound, p. 45. https://doi.org/10.1007/978-3-662-57265-8_7

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.determinant_lower (n : ℕ) (hn : 2 ≤ n) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ, SignMatrix A ∧ Real.sqrt (n.factorial : ℝ) < A.det := by sorry
