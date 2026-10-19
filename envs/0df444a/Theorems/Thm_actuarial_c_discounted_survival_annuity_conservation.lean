-- Prove2me | Theorems.Thm_actuarial_c_discounted_survival_annuity_conservation
-- name    : actuarial_c_discounted_survival_annuity_conservation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:22:55.174987+00:00
-- url     : https://prove2.me/theorems/97e17f53-f3f8-41ad-bbb3-7d3e40054909
-- title:
--   Finite discounted death–annuity summation identity
-- statement:
--   For any real survival sequence, discount v and number of years n, prove the weighted year-to-year survival decrements plus effective-discounted annuity due cashflows plus terminal survival value equal initial survival mass. This is the exact discrete-time identity that underlies the conventional finite insurance–annuity relationship, including the zero-horizon boundary.
--
--   The original mathematical identity is an open formal mission target. Its type has been copied exactly from a successful private remote Lean proof, which does not establish acceptance of this individual Prove2Me target.
-- source:
--   Original actuarial formalisation informed by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapters 3 and 5. Where the result is pure finite-sum algebra, it is an independently derived supporting identity, not claimed as a verbatim textbook theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

theorem actuarial_c_discounted_survival_annuity_conservation (s : ℕ → ℝ)
    (v : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n,
       v^(j+1) * (s j - s (j+1))) +
      (1-v)*(∑ j ∈ Finset.range n, v^j * s j) +
      v^n * s n = s 0 := by sorry
