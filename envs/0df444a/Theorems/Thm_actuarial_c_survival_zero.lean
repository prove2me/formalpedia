-- Prove2me | Theorems.Thm_actuarial_c_survival_zero
-- name    : actuarial_c_survival_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:59:54.260414+00:00
-- url     : https://prove2.me/theorems/b68e75e6-88a1-4314-80ee-8d031dde219f
-- title:
--   Outset survival is full probability mass
-- statement:
--   Outset survival is full probability mass.
--
--   Mathematical relation:
--
--   $$
--   S(0)=\sum_{k=0}^{h}p_k
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Sections 5.1–5.2, occurrence and death-year timing, printed p. 61. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_total
import Definitions.Def_actuarial_c_surv

open ActuarialAssurances

theorem actuarial_c_survival_zero (h : ℕ) (p : ℕ → ℝ) : surv h p 0=total h p := by sorry
