-- Prove2me | Theorems.Thm_actuarial_f_spouse_payment_after_survivor_zero
-- name    : actuarial_f_spouse_payment_after_survivor_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:13:39.262989+00:00
-- url     : https://prove2.me/theorems/57ec99aa-96fb-4c2b-bb80-b8d9521bfb01
-- title:
--   Spouse payment after survivor zero
-- statement:
--   The spouse's payment amount is zero after the spouse's final eligible payment date.
--
--   The defining or asserted relationship is:
--
--   $$
--   t>j\Longrightarrow C^S_t=0
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §4.4, guaranteed life annuity payments begins at p. 53; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_spouseInstalment

open ActuarialUnderpinsF

theorem actuarial_f_spouse_payment_after_survivor_zero (h z i j t : ℕ)
    (s : ℕ → ℕ → ℝ) (gs : ℕ → ℕ → ℝ)
    (ht : j < t) : spouseInstalment h z i j t s gs = 0 := by sorry
