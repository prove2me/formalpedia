-- Prove2me | Theorems.Thm_BookSixth_log_factorial_mean_eq
-- name    : BookSixth.log_factorial_mean_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T08:44:11.329158+00:00
-- url     : https://prove2.me/theorems/e5e2dbad-49a8-4922-8d7c-ed093b4690e9
-- title:
--   Chapter 37 adapter: mean of logs equals scaled log factorial
-- statement:
--   The mean of log 1 through log r equals (log r!) / r.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, adapter lemma for the entropy proof of the Bregman-Minc bound. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.log_factorial_mean_eq (r : Nat) :
    (∑ k ∈ Finset.Icc 1 r, Real.log (k : Real)) / (r : Real) = Real.log (r.factorial : Real) / (r : Real) := by sorry
