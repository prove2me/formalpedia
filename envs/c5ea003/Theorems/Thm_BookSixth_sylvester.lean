-- Prove2me | Theorems.Thm_BookSixth_sylvester
-- name    : BookSixth.sylvester
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-13T01:37:53.132178+00:00
-- url     : https://prove2.me/theorems/66beac61-578b-42f2-a83e-abce0fed05fa
-- title:
--   Chapter 7, Powers-of-two construction
-- statement:
--   For every nonnegative integer m, there is a real Hadamard matrix of order 2^m, including order one.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 7, Powers-of-two construction, p. 44. https://doi.org/10.1007/978-3-662-57265-8_7

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.sylvester (m : ℕ) :
    ∃ A : Matrix (Fin (2^m)) (Fin (2^m)) ℝ, SignMatrix A ∧
      A.transpose * A = ((2^m : ℕ) : ℝ) • (1 : Matrix (Fin (2^m)) (Fin (2^m)) ℝ) := by sorry
