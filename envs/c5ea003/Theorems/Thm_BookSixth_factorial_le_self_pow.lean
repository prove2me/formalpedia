-- Prove2me | Theorems.Thm_BookSixth_factorial_le_self_pow
-- name    : BookSixth.factorial_le_self_pow
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T06:23:56.527232+00:00
-- url     : https://prove2.me/theorems/29b0e833-849d-470d-ab16-704eae8d0661
-- title:
--   Chapter 37 adapter: factorial bounded by self-power
-- statement:
--   For every n, n! is at most n^n as reals. Each Bregman-Minc factor (r_i!)^{1/r_i} is therefore at most r_i.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, factorial estimate used in the Bregman-Minc assembly, p. 266. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.factorial_le_self_pow (n : ℕ) :
    (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by sorry
