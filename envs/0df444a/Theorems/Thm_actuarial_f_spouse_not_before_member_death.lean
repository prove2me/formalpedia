-- Prove2me | Theorems.Thm_actuarial_f_spouse_not_before_member_death
-- name    : actuarial_f_spouse_not_before_member_death
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:04:17.98111+00:00
-- url     : https://prove2.me/theorems/0239ba99-07ba-4a6b-83b2-30dd4003e8d1
-- title:
--   Spouse not before member death
-- statement:
--   A spouse continuation payment is excluded up to and including the member's death-year endpoint.
--
--   The defining or asserted relationship is:
--
--   $$
--   t\le i\Longrightarrow s_{ij}(t)=0
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §4.4, guaranteed life annuity payments begins at p. 53; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_spouseDue

open ActuarialUnderpinsF

theorem actuarial_f_spouse_not_before_member_death (h i j t : ℕ)
    (ht : t ≤ i) : spouseDue h i j t = 0 := by sorry
