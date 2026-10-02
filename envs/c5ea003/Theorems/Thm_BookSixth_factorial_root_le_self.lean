-- Prove2me | Theorems.Thm_BookSixth_factorial_root_le_self
-- name    : BookSixth.factorial_root_le_self
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T06:33:47.329001+00:00
-- url     : https://prove2.me/theorems/fda7975d-abb9-4a99-8136-8083553e6cd5
-- title:
--   Chapter 37 adapter: rooted factorial bounded by row sum
-- statement:
--   For positive r, (r!)^{1/r} is at most r as reals. Each Bregman-Minc factor is therefore bounded by its row sum.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, rooted factorial estimate used in the Bregman-Minc assembly, p. 266. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.factorial_root_le_self (r : ℕ) (hr : 0 < r) :
    ((r.factorial : ℝ)) ^ ((1 : ℝ) / (r : ℝ)) ≤ (r : ℝ) := by sorry
