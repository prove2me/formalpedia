-- Prove2me | Theorems.Thm_actuarial_f_tranche_floor_zero
-- name    : actuarial_f_tranche_floor_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:16:20.719989+00:00
-- url     : https://prove2.me/theorems/c95dddaa-201c-42e1-b8b1-3c4264276a9c
-- title:
--   Tranche floor zero
-- statement:
--   With no pension tranches there is no pension payable from tranche-level maxima.
--
--   The defining or asserted relationship is:
--
--   $$
--   K=0\Longrightarrow U_{\text{tranche}}=0
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapter 17 (embedded option valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow Chapter 20, financial option contracts begins at p. 337; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_trancheFloorTotal

open ActuarialUnderpinsF

theorem actuarial_f_tranche_floor_zero (a b : ℕ → ℝ) :
    trancheFloorTotal a b 0 = 0 := by sorry
