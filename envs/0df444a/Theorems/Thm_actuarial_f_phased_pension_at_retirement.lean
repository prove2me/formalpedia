-- Prove2me | Theorems.Thm_actuarial_f_phased_pension_at_retirement
-- name    : actuarial_f_phased_pension_at_retirement
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:08:35.464591+00:00
-- url     : https://prove2.me/theorems/ba998d88-0715-44c3-ac3d-34e6412ea405
-- title:
--   Phased pension at retirement
-- statement:
--   At retirement the preserved pension includes pre-retirement revaluation, with no extra in-payment anniversary increase.
--
--   The defining or asserted relationship is:
--
--   $$
--   P_r=P_{\text{exit}}R_r
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §13.3.1, defined benefit pension plans begins at p. 204; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_deferredIncrease
import Definitions.Def_actuarial_f_phasedPension

open ActuarialUnderpinsF

theorem actuarial_f_phased_pension_at_retirement (base : ℝ) (r : ℕ)
    (reval increase : ℕ → ℝ) :
    phasedPension base r r reval increase = base * deferredIncrease r reval := by sorry
