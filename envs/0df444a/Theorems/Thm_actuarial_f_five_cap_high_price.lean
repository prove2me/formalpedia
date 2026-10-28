-- Prove2me | Theorems.Thm_actuarial_f_five_cap_high_price
-- name    : actuarial_f_five_cap_high_price
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:06:53.473933+00:00
-- url     : https://prove2.me/theorems/24ce7339-fc8e-4c31-98e6-229b35bd04d9
-- title:
--   Five cap high price
-- statement:
--   With zero floor and five per cent cap, an eight per cent increase is restricted to five per cent.
--
--   The defining or asserted relationship is:
--
--   $$
--   \ell(0,0.05,0.08)=0.05
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §13.3.1, defined benefit pension plans begins at p. 204; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_lpiRate

open ActuarialUnderpinsF

theorem actuarial_f_five_cap_high_price :
    lpiRate 0 (5/100 : ℝ) (8/100) = (5/100 : ℝ) := by sorry
