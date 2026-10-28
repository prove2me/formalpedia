-- Prove2me | Theorems.Thm_actuarial_f_spouse_fixed_base_above_first
-- name    : actuarial_f_spouse_fixed_base_above_first
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:12:41.217181+00:00
-- url     : https://prove2.me/theorems/90b4d4c8-2451-4005-acb6-2fafa6ce3183
-- title:
--   Spouse fixed base above first
-- statement:
--   A spouse minimum selected at member death exceeds the first contingent benefit base calculated at death.
--
--   The defining or asserted relationship is:
--
--   $$
--   S_{zi}\ge S^A_{zi}
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §4.4, guaranteed life annuity payments begins at p. 53; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_spouseBaseAtDeath

open ActuarialUnderpinsF

theorem actuarial_f_spouse_fixed_base_above_first (z i : ℕ)
    (a b : ℕ → ℕ → ℝ) :
    a z i ≤ spouseBaseAtDeath z i a b := by sorry
