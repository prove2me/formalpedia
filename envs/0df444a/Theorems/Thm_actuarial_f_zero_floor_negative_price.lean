-- Prove2me | Theorems.Thm_actuarial_f_zero_floor_negative_price
-- name    : actuarial_f_zero_floor_negative_price
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:06:43.868897+00:00
-- url     : https://prove2.me/theorems/c8ad764e-3a21-4666-8afb-1eb341eddfb7
-- title:
--   Zero floor negative price
-- statement:
--   With zero floor and five per cent cap, a negative two per cent price change produces no annual pension reduction.
--
--   The defining or asserted relationship is:
--
--   $$
--   \ell(0,0.05,-0.02)=0
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapter 17 (embedded option valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow Chapter 20, financial option contracts begins at p. 337; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_lpiRate

open ActuarialUnderpinsF

theorem actuarial_f_zero_floor_negative_price : 
    lpiRate 0 (5/100 : ℝ) (-2/100) = 0 := by sorry
