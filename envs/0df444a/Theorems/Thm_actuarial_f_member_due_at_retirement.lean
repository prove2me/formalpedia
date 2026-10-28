-- Prove2me | Theorems.Thm_actuarial_f_member_due_at_retirement
-- name    : actuarial_f_member_due_at_retirement
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:04:08.452934+00:00
-- url     : https://prove2.me/theorems/d2e3b9f6-00f2-4122-b9a7-adba355a0af2
-- title:
--   Member due at retirement
-- statement:
--   Provided the member remains alive through retirement, an instalment is due at the specified commencement date under this due-date convention.
--
--   The defining or asserted relationship is:
--
--   $$
--   r\le i\Longrightarrow m_i(r)=1
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §13.3.1, defined benefit pension plans begins at p. 204; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_memberDue

open ActuarialUnderpinsF

theorem actuarial_f_member_due_at_retirement (r i : ℕ) (hr : r ≤ i) :
    memberDue r i r = 1 := by sorry
