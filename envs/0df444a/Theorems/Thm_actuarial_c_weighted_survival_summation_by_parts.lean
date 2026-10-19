-- Prove2me | Theorems.Thm_actuarial_c_weighted_survival_summation_by_parts
-- name    : actuarial_c_weighted_survival_summation_by_parts
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:23:27.222994+00:00
-- url     : https://prove2.me/theorems/5359bb90-4377-49fb-8de2-69332ee79725
-- title:
--   Finite weighted survival summation by parts
-- statement:
--   Prove discrete summation by parts for arbitrary real benefit weights b_j and cashflow sequence f_j, with all changes in benefit weights charged to the following period and a separate terminal boundary term. This is the general algebraic identity required to distinguish level assurance/annuity relationships from varying-sum-assured policies.
--
--   The original mathematical identity is an open formal mission target. Its type has been copied exactly from a successful private remote Lean proof, which does not establish acceptance of this individual Prove2Me target.
-- source:
--   Original actuarial formalisation informed by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapters 3 and 5. Where the result is pure finite-sum algebra, it is an independently derived supporting identity, not claimed as a verbatim textbook theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

theorem actuarial_c_weighted_survival_summation_by_parts
    (b f : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), b j * (f j - f (j+1))) +
      b n * f (n+1) =
      b 0 * f 0 +
        ∑ j ∈ Finset.range n, (b (j+1) - b j) * f (j+1) := by sorry
