-- Prove2me | Theorems.Thm_actuarial_f_lpi_growth_nonnegative
-- name    : actuarial_f_lpi_growth_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:19:25.603853+00:00
-- url     : https://prove2.me/theorems/65efc245-2c60-4bef-af32-8c3ee5c380bd
-- title:
--   Lpi growth nonnegative
-- statement:
--   An annual rate collar with nonnegative floor and ordered cap produces nonnegative compounded pension growth.
--
--   The defining or asserted relationship is:
--
--   $$
--   0\le f\le c\Longrightarrow G^{\text{LPI}}_t\ge0
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §13.3.1, defined benefit pension plans begins at p. 204; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_lpiGrowth

open ActuarialUnderpinsF

theorem actuarial_f_lpi_growth_nonnegative (floor cap : ℝ)
    (inflation : ℕ → ℝ) (t : ℕ)
    (hf : 0 ≤ floor) (hfc : floor ≤ cap) :
    0 ≤ lpiGrowth floor cap inflation t := by sorry
