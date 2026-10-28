-- Prove2me | Theorems.Thm_actuarial_f_fixed_award_below_annual_floor
-- name    : actuarial_f_fixed_award_below_annual_floor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:10:15.521463+00:00
-- url     : https://prove2.me/theorems/f2beeea3-e350-4a95-a376-df44b9bf9fbe
-- title:
--   Fixed award below annual floor
-- statement:
--   A repeatedly assessed floor dominates the payment following the elected award alternative's own increase stream.
--
--   The defining or asserted relationship is:
--
--   $$
--   F^{\text{annual}}_{zt}\ge F_{zt}
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapter 17 (embedded option valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), Chapter 20 (financial options), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow Chapter 20, financial option contracts begins at p. 337; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_annualFloorPayment
import Definitions.Def_actuarial_f_fixedChoicePayment

open ActuarialUnderpinsF

theorem actuarial_f_fixed_award_below_annual_floor (a b ga gb : ℕ → ℝ)
    (z t : ℕ) :
    fixedChoicePayment a b ga gb z t ≤ annualFloorPayment a b ga gb z t := by sorry
