-- Prove2me | Theorems.Thm_actuarial_c_discounted_tail_telescope
-- name    : actuarial_c_discounted_tail_telescope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:23:02.825141+00:00
-- url     : https://prove2.me/theorems/f7212a73-6c84-4411-ba3a-d8da5bba2328
-- title:
--   Finite discounted survival telescoping
-- statement:
--   Show for any real sequence s and discount v that the sum of the year-by-year differences v^j s_j minus v^(j+1) s_(j+1) equals initial survival mass minus the single exact terminal discounted mass v^n s_n. The zero-term n=0 case is included, and no mortality positivity assumption is needed for this purely algebraic identity.
--
--   The original mathematical identity is an open formal mission target. Its type has been copied exactly from a successful private remote Lean proof, which does not establish acceptance of this individual Prove2Me target.
-- source:
--   Original actuarial formalisation informed by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapters 3 and 5. Where the result is pure finite-sum algebra, it is an independently derived supporting identity, not claimed as a verbatim textbook theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

theorem actuarial_c_discounted_tail_telescope (s : ℕ → ℝ) (v : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n,
       (v^j * s j - v^(j+1) * s (j+1))) = s 0 - v^n * s n := by sorry
