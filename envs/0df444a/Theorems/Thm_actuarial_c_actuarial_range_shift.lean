-- Prove2me | Theorems.Thm_actuarial_c_actuarial_range_shift
-- name    : actuarial_c_actuarial_range_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:22:38.480255+00:00
-- url     : https://prove2.me/theorems/c5c99a5b-475f-4ef8-8338-96f7aa76213e
-- title:
--   Finite annuity payment-index shift
-- statement:
--   Show that the sum over payment indices 0 through n equals the initial payment plus the sum over n shifted indices j+1. The statement includes the n=0 case and is required to express the increasing-benefit insurance–annuity identity with a payment at the start of the policy year.
--
--   The original mathematical identity is an open formal mission target. Its type has been copied exactly from a successful private remote Lean proof, which does not establish acceptance of this individual Prove2Me target.
-- source:
--   Original actuarial formalisation informed by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapters 3 and 5. Where the result is pure finite-sum algebra, it is an independently derived supporting identity, not claimed as a verbatim textbook theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

theorem actuarial_c_actuarial_range_shift (f : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), f j) =
      f 0 + ∑ j ∈ Finset.range n, f (j+1) := by sorry
