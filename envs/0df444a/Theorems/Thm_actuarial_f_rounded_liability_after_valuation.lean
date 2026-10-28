-- Prove2me | Theorems.Thm_actuarial_f_rounded_liability_after_valuation
-- name    : actuarial_f_rounded_liability_after_valuation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:21:23.942593+00:00
-- url     : https://prove2.me/theorems/6cddc78d-e9c6-4eb7-b0e3-6aa88e0fae22
-- title:
--   Rounded liability after valuation
-- statement:
--   Applying a contractual final rounding operator after valuation gives the same result for the two equivalent actuarial valuation representations.
--
--   The defining or asserted relationship is:
--
--   $$
--   \mathcal R_{\rho,D}(V_{\text{direct}})=\mathcal R_{\rho,D}(V_{\text{state}})
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §13.3.1, defined benefit pension plans begins at p. 204; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_finalRounded
import Definitions.Def_actuarial_f_roundedDirectEPV
import Definitions.Def_actuarial_f_stateEPV

open ActuarialUnderpinsF

theorem actuarial_f_rounded_liability_after_valuation
    (n h r g : ℕ) (p : ℕ → ℕ → ℕ → ℝ)
    (disc : ℕ → ℝ) (a b c : ℕ → ℝ)
    (s : ℕ → ℕ → ℝ) (estate g0 g1 : ℕ → ℝ)
    (gs : ℕ → ℕ → ℝ) (ge : ℕ → ℝ)
    (quantum : ℝ) (roundUnit : ℝ → ℝ) :
    roundedDirectEPV n h r g p disc a b c s estate
      g0 g1 gs ge quantum roundUnit =
    finalRounded (stateEPV n h r g p disc a b c s estate g0 g1 gs ge)
      quantum roundUnit := by sorry
