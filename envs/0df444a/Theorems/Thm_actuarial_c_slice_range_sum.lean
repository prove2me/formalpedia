-- Prove2me | Theorems.Thm_actuarial_c_slice_range_sum
-- name    : actuarial_c_slice_range_sum
-- status  : Open
-- author  : @WillR
-- created : 2026-10-13T06:23:20.450012+00:00
-- url     : https://prove2.me/theorems/4e98474f-e43b-4b82-b4ba-b14936d3e8cb
-- title:
--   Half-open deferred-period summation
-- statement:
--   With a, n and h nonnegative integers and a+n at most h, show that a finite horizon sum restricted to a <= j < a+n equals a sum over n deferred indices with the argument j=a+r. The endpoints are disjoint, ensuring no death-period payment is counted twice when term cover is decomposed into immediate and deferred terms.
--
--   The original mathematical identity is an open formal mission target. Its type has been copied exactly from a successful private remote Lean proof, which does not establish acceptance of this individual Prove2Me target.
-- source:
--   Original actuarial formalisation informed by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapters 3 and 5. Where the result is pure finite-sum algebra, it is an independently derived supporting identity, not claimed as a verbatim textbook theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals

theorem actuarial_c_slice_range_sum (h a n : ℕ) (f : ℕ → ℝ)
    (han : a+n ≤ h) :
    (∑ j ∈ Finset.range h, if a ≤ j ∧ j < a+n then f j else 0) =
       ∑ j ∈ Finset.range n, f (a+j) := by sorry
