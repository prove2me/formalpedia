-- Prove2me | Theorems.Thm_actuarial_c_finite_assurance_annuity
-- name    : actuarial_c_finite_assurance_annuity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T21:25:59.151295+00:00
-- url     : https://prove2.me/theorems/72f053d8-196f-4b59-bfd1-2ccf2f0fb6d6
-- title:
--   Annual finite death/maturity and annuity due discount conservation
-- statement:
--   Annual finite death/maturity and annuity due discount conservation.
--
--   Mathematical relation:
--
--   $$
--   A^{1}_{n|}+v^nS(n)+(1-v)\ddot a_n=1
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
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_term
import Definitions.Def_actuarial_c_pureMass
import Definitions.Def_actuarial_c_due

open ActuarialAssurances

theorem actuarial_c_finite_assurance_annuity (h n : ℕ) (v : ℝ) (p : ℕ → ℝ) (hn : n ≤ h) (hm : total h p=1) : term h n v (fun _ => 1) p+pureMass h n v p+(1-v)*due h n v p=1 := by sorry
