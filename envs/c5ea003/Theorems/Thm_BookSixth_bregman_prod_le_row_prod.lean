-- Prove2me | Theorems.Thm_BookSixth_bregman_prod_le_row_prod
-- name    : BookSixth.bregman_prod_le_row_prod
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T06:39:28.282367+00:00
-- url     : https://prove2.me/theorems/4132324b-4d64-4c41-9bb3-e4a16b884206
-- title:
--   Chapter 37 adapter: Bregman product bounded by row-sum product
-- statement:
--   When every row sum is positive, the Bregman-Minc product over i of (r_i!)^{1/r_i} is at most the product of the row sums.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, product assembly used with the Bregman-Minc bound, p. 266. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.bregman_prod_le_row_prod (n : ℕ) (r : Fin n → ℕ) (hpos : ∀ i, 0 < r i) :
    ∏ i, ((r i).factorial : ℝ) ^ ((1 : ℝ) / (r i : ℝ)) ≤ ∏ i, (r i : ℝ) := by sorry
