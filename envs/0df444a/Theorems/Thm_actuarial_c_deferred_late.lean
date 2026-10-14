-- Prove2me | Theorems.Thm_actuarial_c_deferred_late
-- name    : actuarial_c_deferred_late
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:18:54.528486+00:00
-- url     : https://prove2.me/theorems/e1540447-fc87-4209-b75b-85f9222078d7
-- title:
--   Waiting until terminal horizon gives no covered year
-- statement:
--   Waiting until terminal horizon gives no covered year.
--
--   Mathematical relation:
--
--   $$
--   {}_{a|}A^{1}_{n|}=0,\quad a\ge h
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.3, term and whole life insurance, printed p. 64. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_deferred

open ActuarialAssurances

theorem actuarial_c_deferred_late (h a n : ℕ) (v : ℝ) (b p : ℕ → ℝ) (ha : h ≤ a) : deferred h a n v b p=0 := by sorry
