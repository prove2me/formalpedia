-- Prove2me | Theorems.Thm_actuarial_c_survival_after_horizon
-- name    : actuarial_c_survival_after_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:15:21.826149+00:00
-- url     : https://prove2.me/theorems/7660177c-30b2-43ca-8370-f59f6d874aa8
-- title:
--   Survival beyond terminal censored date is unspecified and excluded
-- statement:
--   Survival beyond terminal censored date is unspecified and excluded.
--
--   Mathematical relation:
--
--   $$
--   S(j)=0,\quad j>h
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Sections 5.1–5.2, occurrence and death-year timing, printed p. 61. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_surv

open ActuarialAssurances

theorem actuarial_c_survival_after_horizon (h j : ℕ) (p : ℕ → ℝ) (hj : h < j) : surv h p j=0 := by sorry
