-- Prove2me | Theorems.Thm_actuarial_f_additive_at_base
-- name    : actuarial_f_additive_at_base
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:07:53.127252+00:00
-- url     : https://prove2.me/theorems/53676b5b-5209-426b-b8a2-d4940fc4cb36
-- title:
--   Additive at base
-- statement:
--   The additive growth approximation starts at one before annual price changes.
--
--   The defining or asserted relationship is:
--
--   $$
--   G^{\text{add}}_0=1
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §13.3.1, defined benefit pension plans begins at p. 204; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_additiveGrowth

open ActuarialUnderpinsF

theorem actuarial_f_additive_at_base (r : ℕ → ℝ) :
    additiveGrowth r 0 = 1 := by sorry
