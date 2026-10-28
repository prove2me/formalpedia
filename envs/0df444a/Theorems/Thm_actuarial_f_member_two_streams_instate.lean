-- Prove2me | Theorems.Thm_actuarial_f_member_two_streams_instate
-- name    : actuarial_f_member_two_streams_instate
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:17:54.158835+00:00
-- url     : https://prove2.me/theorems/7bbae34e-fc7b-4dd5-9f2f-a359754ee6c8
-- title:
--   Member two streams instate
-- statement:
--   Two independently indexed tranche payments share the same living-member state and can be factored by its due-date indicator.
--
--   The defining or asserted relationship is:
--
--   $$
--   C^{(1)}_t+C^{(2)}_t=(U_zG^{(1)}_t+C_zG^{(2)}_t)m_i(t)
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §15.3, stochastic life annuity valuation begins at p. 229; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_awardBase
import Definitions.Def_actuarial_f_memberDue
import Definitions.Def_actuarial_f_memberTrancheOne
import Definitions.Def_actuarial_f_memberTrancheTwo

open ActuarialUnderpinsF

theorem actuarial_f_member_two_streams_instate (r z i t : ℕ)
    (a b c g0 g1 : ℕ → ℝ) :
    memberTrancheOne r z i t a b g0 + memberTrancheTwo r z i t c g1 =
    (awardBase a b z * g0 t + c z * g1 t) * memberDue r i t := by sorry
