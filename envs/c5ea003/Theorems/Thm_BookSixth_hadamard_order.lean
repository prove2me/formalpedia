-- Prove2me | Theorems.Thm_BookSixth_hadamard_order
-- name    : BookSixth.hadamard_order
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-13T01:36:38.890325+00:00
-- url     : https://prove2.me/theorems/9f3d1609-d6cf-4e6f-96ee-d1578525e991
-- title:
--   Chapter 7, Hadamard order restriction
-- statement:
--   A real sign matrix of order n greater than 2 with orthogonal columns must have order divisible by 4.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 7, Hadamard order restriction, p. 44. https://doi.org/10.1007/978-3-662-57265-8_7

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.hadamard_order {n : ℕ} (hn : 2 < n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : SignMatrix A) (horth : A.transpose * A = (n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) :
    4 ∣ n := by sorry
