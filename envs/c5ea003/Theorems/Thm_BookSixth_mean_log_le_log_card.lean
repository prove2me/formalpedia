-- Prove2me | Theorems.Thm_BookSixth_mean_log_le_log_card
-- name    : BookSixth.mean_log_le_log_card
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T08:49:01.836109+00:00
-- url     : https://prove2.me/theorems/18e2bd32-8128-4e85-bf2d-8d556126d1c2
-- title:
--   Chapter 37 adapter: mean of logs bounded by log of count
-- statement:
--   The mean of log 1 through log r is at most log r.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, adapter lemma for the entropy proof of the Bregman-Minc bound. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.mean_log_le_log_card (r : Nat) (hr : 0 < r) :
    (∑ k ∈ Finset.Icc 1 r, Real.log (k : Real)) / (r : Real) ≤ Real.log (r : Real) := by sorry
