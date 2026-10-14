-- Prove2me | Theorems.Thm_actuarial_c_deferred_now
-- name    : actuarial_c_deferred_now
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T21:19:19.948315+00:00
-- url     : https://prove2.me/theorems/e7e442ce-09f3-4aea-9dd3-6e8bdb8ff01f
-- title:
--   Zero waiting period reduces to ordinary term cover
-- statement:
--   Zero waiting period reduces to ordinary term cover.
--
--   Mathematical relation:
--
--   $$
--   {}_{0|}A^{1}_{n|}=A^{1}_{n|}
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.3, term and whole life insurance, printed p. 64. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_term
import Definitions.Def_actuarial_c_deferred

open ActuarialAssurances

theorem actuarial_c_deferred_now (h n : ℕ) (v : ℝ) (b p : ℕ → ℝ) (hn : n ≤ h) : deferred h 0 n v b p=term h n v b p := by sorry
