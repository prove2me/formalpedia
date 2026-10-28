-- Prove2me | Theorems.Thm_actuarial_f_award_idempotent
-- name    : actuarial_f_award_idempotent
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:09:41.583468+00:00
-- url     : https://prove2.me/theorems/55fe348a-074f-4c69-a3ae-dd89dcbc7e31
-- title:
--   Award idempotent
-- statement:
--   Identical contractual pension alternatives produce exactly the same award amount.
--
--   The defining or asserted relationship is:
--
--   $$
--   \max(A_z,A_z)=A_z
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapter 17 (embedded option valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), Chapter 20 (financial options), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow Chapter 20, financial option contracts begins at p. 337; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_awardBase

open ActuarialUnderpinsF

theorem actuarial_f_award_idempotent (a : ℕ → ℝ) (z : ℕ) :
    awardBase a a z = a z := by sorry
