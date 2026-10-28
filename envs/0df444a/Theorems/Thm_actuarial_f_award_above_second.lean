-- Prove2me | Theorems.Thm_actuarial_f_award_above_second
-- name    : actuarial_f_award_above_second
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:09:17.892873+00:00
-- url     : https://prove2.me/theorems/eda0663c-9cc1-4500-8344-c1e8a68b1dfe
-- title:
--   Award above second
-- statement:
--   The one-time award maximum cannot be smaller than the second contractual award alternative.
--
--   The defining or asserted relationship is:
--
--   $$
--   U_z\ge B_z
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapter 17 (embedded option valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), Chapter 20 (financial options), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow Chapter 20, financial option contracts begins at p. 337; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_awardBase

open ActuarialUnderpinsF

theorem actuarial_f_award_above_second (a b : ℕ → ℝ) (z : ℕ) :
    b z ≤ awardBase a b z := by sorry
