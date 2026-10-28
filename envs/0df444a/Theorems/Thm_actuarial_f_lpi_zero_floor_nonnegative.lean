-- Prove2me | Theorems.Thm_actuarial_f_lpi_zero_floor_nonnegative
-- name    : actuarial_f_lpi_zero_floor_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:08:13.342848+00:00
-- url     : https://prove2.me/theorems/b43c6e13-ab31-4c43-af81-ee15b0fe7a3b
-- title:
--   Lpi zero floor nonnegative
-- statement:
--   A zero annual increase floor gives a nonnegative applied annual rate when the cap is nonnegative.
--
--   The defining or asserted relationship is:
--
--   $$
--   c\ge0\Longrightarrow\ell(0,c,\pi)\ge0
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapter 17 (embedded option valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow Chapter 20, financial option contracts begins at p. 337; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_lpiRate

open ActuarialUnderpinsF

theorem actuarial_f_lpi_zero_floor_nonnegative (cap observed : ℝ)
    (hc : 0 ≤ cap) : 0 ≤ lpiRate 0 cap observed := by sorry
