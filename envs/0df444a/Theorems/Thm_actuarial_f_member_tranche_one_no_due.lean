-- Prove2me | Theorems.Thm_actuarial_f_member_tranche_one_no_due
-- name    : actuarial_f_member_tranche_one_no_due
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:17:28.885321+00:00
-- url     : https://prove2.me/theorems/ab0919ce-9b46-4a7f-8afa-f8cf50f7a438
-- title:
--   Member tranche one no due
-- statement:
--   A first-tranche award underpin cannot generate member payments after member death.
--
--   The defining or asserted relationship is:
--
--   $$
--   t>i\Longrightarrow C^{(1)}_t=0
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §13.3.1, defined benefit pension plans begins at p. 204; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_memberTrancheOne

open ActuarialUnderpinsF

theorem actuarial_f_member_tranche_one_no_due (r z i t : ℕ)
    (a b g0 : ℕ → ℝ) (ht : i < t) :
    memberTrancheOne r z i t a b g0 = 0 := by sorry
