-- Prove2me | Theorems.Thm_actuarial_f_member_tranche_two_before_award
-- name    : actuarial_f_member_tranche_two_before_award
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:17:40.717155+00:00
-- url     : https://prove2.me/theorems/8b6c5781-c407-4765-997f-376fb0b375c4
-- title:
--   Member tranche two before award
-- statement:
--   The second tranche has no member payment before pension commencement.
--
--   The defining or asserted relationship is:
--
--   $$
--   t<r\Longrightarrow C^{(2)}_t=0
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapter 17 (embedded option valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), Chapter 20 (financial options), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow Chapter 20, financial option contracts begins at p. 337; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_memberTrancheTwo

open ActuarialUnderpinsF

theorem actuarial_f_member_tranche_two_before_award (r z i t : ℕ)
    (c g1 : ℕ → ℝ) (ht : t < r) :
    memberTrancheTwo r z i t c g1 = 0 := by sorry
