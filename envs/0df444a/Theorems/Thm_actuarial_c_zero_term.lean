-- Prove2me | Theorems.Thm_actuarial_c_zero_term
-- name    : actuarial_c_zero_term
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:17:37.498119+00:00
-- url     : https://prove2.me/theorems/a29c2697-8f29-4587-8303-5845bbf91818
-- title:
--   Zero-term cover has no death events
-- statement:
--   Zero-term cover has no death events.
--
--   Mathematical relation:
--
--   $$
--   A^{1}_{0|}=0
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

open ActuarialAssurances

theorem actuarial_c_zero_term (h : ℕ) (v : ℝ) (b p : ℕ → ℝ) : term h 0 v b p=0 := by sorry
