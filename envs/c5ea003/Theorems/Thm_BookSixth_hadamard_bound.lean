-- Prove2me | Theorems.Thm_BookSixth_hadamard_bound
-- name    : BookSixth.hadamard_bound
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-13T01:36:31.651222+00:00
-- url     : https://prove2.me/theorems/41cc7bd7-ed60-4cfc-8092-61691bd1a85a
-- title:
--   Chapter 7, Equation (5): determinant bound
-- statement:
--   For a positive order n and a real sign matrix A, the absolute determinant is at most n raised to the real power n/2.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 7, Equation (5): determinant bound, p. 43. https://doi.org/10.1007/978-3-662-57265-8_7

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.hadamard_bound {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : SignMatrix A) :
    |A.det| ≤ (n : ℝ) ^ ((n : ℝ) / 2) := by sorry
