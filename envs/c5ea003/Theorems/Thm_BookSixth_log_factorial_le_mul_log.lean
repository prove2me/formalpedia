-- Prove2me | Theorems.Thm_BookSixth_log_factorial_le_mul_log
-- name    : BookSixth.log_factorial_le_mul_log
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T06:44:59.594364+00:00
-- url     : https://prove2.me/theorems/6ed02909-f67a-48d9-9b06-97cfb653e44e
-- title:
--   Chapter 37 adapter: log-factorial entropy bound
-- statement:
--   For every r, log(r!) is at most r * log r. Log-domain form of the factorial estimate feeding the entropy assembly for Bregman-Minc.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, log-factorial estimate used in the entropy route to Bregman-Minc, p. 266. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.log_factorial_le_mul_log (r : ℕ) :
    Real.log (r.factorial : ℝ) ≤ (r : ℝ) * Real.log (r : ℝ) := by sorry
