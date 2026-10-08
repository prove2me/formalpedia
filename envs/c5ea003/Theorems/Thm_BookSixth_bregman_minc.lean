-- Prove2me | Theorems.Thm_BookSixth_bregman_minc
-- name    : BookSixth.bregman_minc
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-13T01:37:03.056953+00:00
-- url     : https://prove2.me/theorems/27f69488-3b06-47c0-81b4-d3eaeb21d9f0
-- title:
--   Chapter 37, Theorem 1: permanent upper bound
-- statement:
--   For a zero-one square matrix with positive row sums d_i, its permanent is at most the product of (d_i!)^(1/d_i), using real exponents. Zero-row matrices have permanent zero and are handled separately; this target does not interpret division by zero as a row-sum convention.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, Theorem 1: permanent upper bound, p. 262. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.bregman_minc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ) (hA : ∀ i j, A i j ≤ 1) (hrows : ∀ i, 0 < ∑ j, A i j) :
    (permanent A : ℝ) ≤ ∏ i, ((Nat.factorial (∑ j, A i j) : ℕ) : ℝ) ^
      (1 / ((∑ j, A i j : ℕ) : ℝ)) := by sorry
