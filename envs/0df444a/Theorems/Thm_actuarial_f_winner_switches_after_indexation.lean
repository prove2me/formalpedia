-- Prove2me | Theorems.Thm_actuarial_f_winner_switches_after_indexation
-- name    : actuarial_f_winner_switches_after_indexation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:11:10.472162+00:00
-- url     : https://prove2.me/theorems/89f46934-3a4d-40ac-aedb-f6d851bb73cd
-- title:
--   Winner switches after indexation
-- statement:
--   A once-elected annual pension of one hundred and twenty differs from an annual floor of three hundred after the alternative's threefold increase.
--
--   The defining or asserted relationship is:
--
--   $$
--   F_{z1}=120<300=F^{\text{annual}}_{z1}
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §13.3.1, defined benefit pension plans begins at p. 204; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_annualFloorPayment
import Definitions.Def_actuarial_f_fixedChoicePayment

open ActuarialUnderpinsF

theorem actuarial_f_winner_switches_after_indexation :
    let a : ℕ → ℝ := fun _ => 120
    let b : ℕ → ℝ := fun _ => 100
    let ga : ℕ → ℝ := fun _ => 1
    let gb : ℕ → ℝ := fun t => if t = 0 then 1 else 3
    fixedChoicePayment a b ga gb 0 1 = 120 ∧
      annualFloorPayment a b ga gb 0 1 = 300 := by sorry
