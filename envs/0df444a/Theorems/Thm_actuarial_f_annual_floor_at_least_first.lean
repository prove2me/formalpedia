-- Prove2me | Theorems.Thm_actuarial_f_annual_floor_at_least_first
-- name    : actuarial_f_annual_floor_at_least_first
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:09:49.404921+00:00
-- url     : https://prove2.me/theorems/d9fde43f-a60b-4197-aee4-a149452c3bcc
-- title:
--   Annual floor at least first
-- statement:
--   A payment-date comparison is at least the first current indexed pension amount.
--
--   The defining or asserted relationship is:
--
--   $$
--   F^{\text{annual}}_{zt}\ge A_zG^A_t
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapter 17 (embedded option valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow Chapter 20, financial option contracts begins at p. 337; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_annualFloorPayment

open ActuarialUnderpinsF

theorem actuarial_f_annual_floor_at_least_first (a b ga gb : ℕ → ℝ)
    (z t : ℕ) : a z * ga t ≤ annualFloorPayment a b ga gb z t := by sorry
