-- Prove2me | Theorems.Thm_BookSixth_latin_upper_prod_pos
-- name    : BookSixth.latin_upper_prod_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T00:04:16.073651+00:00
-- url     : https://prove2.me/theorems/c9d8051d-1639-43e9-908f-1c576cb15852
-- title:
--   Chapter 37 adapter: positivity of the upper-bound product
-- statement:
--   For every $n$, the upper-bound product $\prod_{k=1}^n (k!)^{n/k}$ from Chapter 37, Theorem 2 is strictly positive.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, Theorem 2 upper-bound positivity adapter, p. 266. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.latin_upper_prod_pos (n : ℕ) :
    0 < ∏ k ∈ Finset.Icc 1 n, (k.factorial : ℝ) ^ ((n : ℝ) / (k : ℝ)) := by sorry
