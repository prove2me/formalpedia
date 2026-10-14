-- Prove2me | Theorems.Thm_actuarial_c_deferred_split
-- name    : actuarial_c_deferred_split
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T21:19:07.163984+00:00
-- url     : https://prove2.me/theorems/a73f279b-fc78-48e6-811c-41e5992db0d3
-- title:
--   Earlier deaths and post-deferral deaths partition the extended term
-- statement:
--   Earlier deaths and post-deferral deaths partition the extended term.
--
--   Mathematical relation:
--
--   $$
--   A^{1}_{a+n|}=A^{1}_{a|}+{}_{a|}A^{1}_{n|}
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

theorem actuarial_c_deferred_split (h a n : ℕ) (v : ℝ) (b p : ℕ → ℝ) (han : a+n ≤ h) : term h (a+n) v b p=term h a v b p+deferred h a n v b p := by sorry
