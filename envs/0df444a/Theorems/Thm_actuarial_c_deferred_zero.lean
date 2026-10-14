-- Prove2me | Theorems.Thm_actuarial_c_deferred_zero
-- name    : actuarial_c_deferred_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:18:42.556965+00:00
-- url     : https://prove2.me/theorems/c6b99491-8209-42d5-a818-672d506dbc2e
-- title:
--   No post-waiting term generates no claim
-- statement:
--   No post-waiting term generates no claim.
--
--   Mathematical relation:
--
--   $$
--   {}_{a|}A^{1}_{0|}=0
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.3, term and whole life insurance, printed p. 64. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_deferred

open ActuarialAssurances

theorem actuarial_c_deferred_zero (h a : ℕ) (v : ℝ) (b p : ℕ → ℝ) : deferred h a 0 v b p=0 := by sorry
