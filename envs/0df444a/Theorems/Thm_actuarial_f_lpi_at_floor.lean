-- Prove2me | Theorems.Thm_actuarial_f_lpi_at_floor
-- name    : actuarial_f_lpi_at_floor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:06:23.679797+00:00
-- url     : https://prove2.me/theorems/6edc6c8a-4354-4494-b8b6-a776c325a3d5
-- title:
--   Lpi at floor
-- statement:
--   Price change below the floor triggers the contractual lower annual rate.
--
--   The defining or asserted relationship is:
--
--   $$
--   \pi\le f\le c\Longrightarrow\ell(f,c,\pi)=f
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapter 17 (embedded option valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow Chapter 20, financial option contracts begins at p. 337; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_lpiRate

open ActuarialUnderpinsF

theorem actuarial_f_lpi_at_floor (floor cap x : ℝ)
    (hfc : floor ≤ cap) (hx : x ≤ floor) :
    lpiRate floor cap x = floor := by sorry
