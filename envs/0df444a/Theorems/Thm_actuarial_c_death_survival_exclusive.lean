-- Prove2me | Theorems.Thm_actuarial_c_death_survival_exclusive
-- name    : actuarial_c_death_survival_exclusive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:59:42.266511+00:00
-- url     : https://prove2.me/theorems/c6b82369-10cf-4fa5-a64a-5dd7371d07e8
-- title:
--   Pre-maturity death excludes maturity
-- statement:
--   Pre-maturity death excludes maturity.
--
--   Mathematical relation:
--
--   $$
--   \mathbf{1}_{\{K=i\}}\mathbf{1}_{\{K\ge j\}}=0,\quad i<j
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Sections 5.1–5.2, occurrence and death-year timing, printed p. 61. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death

open ActuarialAssurances

theorem actuarial_c_death_survival_exclusive (k i j : ℕ) (hij : i < j) : death k i*alive k j=0 := by sorry
