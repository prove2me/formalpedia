-- Prove2me | Theorems.Thm_actuarial_f_fixed_choice_at_award
-- name    : actuarial_f_fixed_choice_at_award
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:19:36.051059+00:00
-- url     : https://prove2.me/theorems/e0daf020-798c-47a7-acc0-6752bd80e0ac
-- title:
--   Fixed choice at award
-- statement:
--   At the initial award date, a permanently selected alternative with unit growth produces the same pension as the maximum commencement award.
--
--   The defining or asserted relationship is:
--
--   $$
--   F_{z0}=\max(A_z,B_z)\quad(G^A_0=G^B_0=1)
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapter 17 (embedded option valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), Chapter 20 (financial options), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow Chapter 20, financial option contracts begins at p. 337; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_awardBase
import Definitions.Def_actuarial_f_fixedChoicePayment

open ActuarialUnderpinsF

theorem actuarial_f_fixed_choice_at_award (a b : ℕ → ℝ) (z : ℕ) :
    fixedChoicePayment a b (fun _ => 1) (fun _ => 1) z 0 =
      awardBase a b z := by sorry
