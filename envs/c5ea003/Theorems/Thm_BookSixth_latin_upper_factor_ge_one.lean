-- Prove2me | Theorems.Thm_BookSixth_latin_upper_factor_ge_one
-- name    : BookSixth.latin_upper_factor_ge_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T00:10:32.940598+00:00
-- url     : https://prove2.me/theorems/552fca41-9bb2-4151-9d3e-6fe5df9035eb
-- title:
--   Chapter 37 adapter: upper-bound factors are at least one
-- statement:
--   For $k \ge 1$ and any $n$, the upper-bound factor $(k!)^{n/k}$ from Chapter 37, Theorem 2 is at least $1$.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, Theorem 2 upper-bound factor comparison adapter, p. 266. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.latin_upper_factor_ge_one (n k : ℕ) (hk : 1 ≤ k) :
    1 ≤ (k.factorial : ℝ) ^ ((n : ℝ) / (k : ℝ)) := by sorry
