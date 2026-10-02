-- Prove2me | Theorems.Thm_BookSixth_log_factorial_eq_sum_Icc
-- name    : BookSixth.log_factorial_eq_sum_Icc
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T08:32:00.97129+00:00
-- url     : https://prove2.me/theorems/5aaca395-1e85-4009-8303-9fe8474d8e13
-- title:
--   Chapter 37 adapter: log factorial as sum of logs
-- statement:
--   The logarithm of r! equals the sum of logarithms of 1 through r.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, adapter lemma for the entropy proof of the Bregman-Minc bound. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.log_factorial_eq_sum_Icc (r : Nat) :
    Real.log (r.factorial : Real) = ∑ k ∈ Finset.Icc 1 r, Real.log (k : Real) := by sorry
