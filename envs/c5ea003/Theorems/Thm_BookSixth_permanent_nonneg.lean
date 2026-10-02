-- Prove2me | Theorems.Thm_BookSixth_permanent_nonneg
-- name    : BookSixth.permanent_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T00:37:03.525818+00:00
-- url     : https://prove2.me/theorems/cdab445f-c28b-4f83-b345-2b62bfacf3e7
-- title:
--   Chapter 37 adapter: permanent of a nonnegative matrix is nonnegative
-- statement:
--   The permanent of a real matrix with all entries nonnegative is nonnegative. Used throughout the Chapter 37 counting bounds to keep extension-count estimates valid.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, permanent nonnegativity adapter, p. 266. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.permanent_nonneg (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ)
    (hnn : ∀ i j, 0 ≤ M i j) :
    0 ≤ Matrix.permanent M := by sorry
