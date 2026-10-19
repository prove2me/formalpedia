-- Prove2me | Theorems.Thm_actuarial_c_endowment_annuity
-- name    : actuarial_c_endowment_annuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:26:28.544302+00:00
-- url     : https://prove2.me/theorems/03172fc7-fc02-4541-b7bc-76faeef3211f
-- title:
--   Annual endowment and annuity due identity from real events
-- statement:
--   Annual endowment and annuity due identity from real events.
--
--   Mathematical relation:
--
--   $$
--   A^{\text{end}}_{n|}+(1-v)\ddot a_n=1
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.4, endowment insurance, printed p. 65. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_total
import Definitions.Def_actuarial_c_surv
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_purePath
import Definitions.Def_actuarial_c_endowPath
import Definitions.Def_actuarial_c_endow
import Definitions.Def_actuarial_c_due

open ActuarialAssurances

theorem actuarial_c_endowment_annuity (h n : ℕ) (v : ℝ) (p : ℕ → ℝ) (hn : n ≤ h) (hm : total h p=1) : endow h n v (fun _ => 1) p+(1-v)*due h n v p=1 := by sorry
