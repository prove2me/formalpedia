-- Prove2me | Theorems.Thm_actuarial_f_member_before_retirement
-- name    : actuarial_f_member_before_retirement
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:03:48.908697+00:00
-- url     : https://prove2.me/theorems/2a7d92e4-19f5-4b1b-bc25-e4f2af6b61e2
-- title:
--   Member before retirement
-- statement:
--   A living member receives no retirement pension instalment before pension commencement.
--
--   The defining or asserted relationship is:
--
--   $$
--   t<r\Longrightarrow m_i(t)=0
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §13.3.1, defined benefit pension plans begins at p. 204; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_memberDue

open ActuarialUnderpinsF

theorem actuarial_f_member_before_retirement (r i t : ℕ) (ht : t < r) :
    memberDue r i t = 0 := by sorry
