-- Prove2me | Theorems.Thm_actuarial_c_pure_no_interest
-- name    : actuarial_c_pure_no_interest
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:20:09.325174+00:00
-- url     : https://prove2.me/theorems/32298c3e-f175-44a3-97ed-f2abfebe9a51
-- title:
--   No interest makes pure endowment a survival probability
-- statement:
--   No interest makes pure endowment a survival probability.
--
--   Mathematical relation:
--
--   $$
--   {}_nE\big|_{v=1}=S(n)
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.4, endowment insurance, printed p. 65. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_surv
import Definitions.Def_actuarial_c_pureMass

open ActuarialAssurances

theorem actuarial_c_pure_no_interest (h n : ℕ) (p : ℕ → ℝ) : pureMass h n 1 p=surv h p n := by sorry
