-- Prove2me | Theorems.Thm_actuarial_c_whole_censor_identity
-- name    : actuarial_c_whole_censor_identity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T21:26:11.577822+00:00
-- url     : https://prove2.me/theorems/077c99a4-3b39-4e87-a126-8638c38dc20c
-- title:
--   Censored terminal survivor mass remains a separate unpaid death exposure
-- statement:
--   Censored terminal survivor mass remains a separate unpaid death exposure.
--
--   Mathematical relation:
--
--   $$
--   A_h+(1-v)\ddot a_h=1-v^hS(h)
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.7, general insurance–annuity identity, printed p. 71. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_total
import Definitions.Def_actuarial_c_surv
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_epv
import Definitions.Def_actuarial_c_due

open ActuarialAssurances

theorem actuarial_c_whole_censor_identity (h : ℕ) (v : ℝ) (p : ℕ → ℝ) (hm : total h p=1) : epv h v (fun _ => 1) p+(1-v)*due h h v p=1-v^h*surv h p h := by sorry
