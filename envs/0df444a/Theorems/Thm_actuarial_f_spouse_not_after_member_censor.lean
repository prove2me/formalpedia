-- Prove2me | Theorems.Thm_actuarial_f_spouse_not_after_member_censor
-- name    : actuarial_f_spouse_not_after_member_censor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:04:41.05398+00:00
-- url     : https://prove2.me/theorems/5d582b8c-3cdc-446f-ba38-f6c976399029
-- title:
--   Spouse not after member censor
-- statement:
--   When the member remains alive to the horizon-censoring state, no post-death survivor pension arises.
--
--   The defining or asserted relationship is:
--
--   $$
--   s_{Hj}(t)=0
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §4.4, guaranteed life annuity payments begins at p. 53; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_spouseDue

open ActuarialUnderpinsF

theorem actuarial_f_spouse_not_after_member_censor (h j t : ℕ) :
    spouseDue h h j t = 0 := by sorry
