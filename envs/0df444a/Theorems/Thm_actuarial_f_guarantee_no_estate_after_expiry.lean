-- Prove2me | Theorems.Thm_actuarial_f_guarantee_no_estate_after_expiry
-- name    : actuarial_f_guarantee_no_estate_after_expiry
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:14:08.405579+00:00
-- url     : https://prove2.me/theorems/158d3af8-5bc9-4d0c-bb97-2cbd7b5093a0
-- title:
--   Guarantee no estate after expiry
-- statement:
--   Estate guarantee payments cease at the exclusive expiry date, irrespective of the payment rate.
--
--   The defining or asserted relationship is:
--
--   $$
--   t\ge r+g\Longrightarrow C^E_t=0
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §4.4, guaranteed life annuity payments begins at p. 53; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_estateInstalment

open ActuarialUnderpinsF

theorem actuarial_f_guarantee_no_estate_after_expiry (h r g z i t : ℕ)
    (estateBase ge : ℕ → ℝ) (ht : r+g ≤ t) :
    estateInstalment h r g z i t estateBase ge = 0 := by sorry
