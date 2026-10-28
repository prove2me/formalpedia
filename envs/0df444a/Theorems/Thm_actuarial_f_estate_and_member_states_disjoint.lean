-- Prove2me | Theorems.Thm_actuarial_f_estate_and_member_states_disjoint
-- name    : actuarial_f_estate_and_member_states_disjoint
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:15:16.368132+00:00
-- url     : https://prove2.me/theorems/8afcad15-8b68-418e-abc2-f09d99c743d1
-- title:
--   Estate and member states disjoint
-- statement:
--   A post-death estate guarantee continuation and the original living-member pension never occupy the same annual payment state.
--
--   The defining or asserted relationship is:
--
--   $$
--   m_i(t)e_i(t)=0
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §4.4, guaranteed life annuity payments begins at p. 53; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_estateDue
import Definitions.Def_actuarial_f_memberDue

open ActuarialUnderpinsF

theorem actuarial_f_estate_and_member_states_disjoint (h r g i t : ℕ) :
    memberDue r i t * estateDue h r g i t = 0 := by sorry
