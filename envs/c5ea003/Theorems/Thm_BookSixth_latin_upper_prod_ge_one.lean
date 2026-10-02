-- Prove2me | Theorems.Thm_BookSixth_latin_upper_prod_ge_one
-- name    : BookSixth.latin_upper_prod_ge_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T00:15:29.683301+00:00
-- url     : https://prove2.me/theorems/28dea526-0f24-46bd-9eb0-bcb342406628
-- title:
--   Chapter 37 adapter: upper-bound product is at least one
-- statement:
--   For every $n$, the upper-bound product $\prod_{k=1}^n (k!)^{n/k}$ from Chapter 37, Theorem 2 is at least $1$.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, Theorem 2 upper-bound comparison adapter, p. 266. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.latin_upper_prod_ge_one (n : ℕ) :
    1 ≤ ∏ k ∈ Finset.Icc 1 n, (k.factorial : ℝ) ^ ((n : ℝ) / (k : ℝ)) := by sorry
