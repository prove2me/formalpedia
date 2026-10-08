-- Prove2me | Theorems.Thm_BookSixth_hadamard_equality
-- name    : BookSixth.hadamard_equality
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-13T01:36:23.117537+00:00
-- url     : https://prove2.me/theorems/8c27bc02-17a6-4248-8e51-9e14b56882d1
-- title:
--   Chapter 7, Equation (6): equality case
-- statement:
--   A positive-order sign matrix attains the Hadamard determinant bound if and only if its distinct columns are orthogonal.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 7, Equation (6): equality case, p. 43. https://doi.org/10.1007/978-3-662-57265-8_7

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.hadamard_equality {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : SignMatrix A) :
    (|A.det| = (n : ℝ) ^ ((n : ℝ) / 2)) ↔
      ∀ i j, i ≠ j → (∑ k, A k i * A k j) = 0 := by sorry
