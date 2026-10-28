-- Prove2me | Theorems.Thm_actuarial_f_member_and_spouse_states_disjoint
-- name    : actuarial_f_member_and_spouse_states_disjoint
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:15:06.976709+00:00
-- url     : https://prove2.me/theorems/5c32d86c-879b-4a68-81d7-36b1b1b28b5c
-- title:
--   Member and spouse states disjoint
-- statement:
--   The member's living-pension state and the spouse's post-death continuation state never both apply to the same instalment.
--
--   The defining or asserted relationship is:
--
--   $$
--   m_i(t)s_{ij}(t)=0
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §4.4, guaranteed life annuity payments begins at p. 53; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_memberDue
import Definitions.Def_actuarial_f_spouseDue

open ActuarialUnderpinsF

theorem actuarial_f_member_and_spouse_states_disjoint (h r i j t : ℕ) :
    memberDue r i t * spouseDue h i j t = 0 := by sorry
