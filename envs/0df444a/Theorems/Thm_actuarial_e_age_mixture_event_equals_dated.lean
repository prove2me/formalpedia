-- Prove2me | Theorems.Thm_actuarial_e_age_mixture_event_equals_dated
-- name    : actuarial_e_age_mixture_event_equals_dated
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T20:19:38.369923+00:00
-- url     : https://prove2.me/theorems/aac48ac3-c00c-491f-bab9-9b38013b5ff8
-- title:
--   Age-difference mixture preserves event/date actuarial equivalence
-- statement:
--   Age-difference mixture preserves event/date actuarial equivalence. Every scenario has its own survival and qualification model, yet summing the scenario-specific event and cashflow valuations gives the same result. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   V_{\text{event}}^{\text{mix}}(\eta)=V_{\text{dated}}^{\text{mix}}(\eta)
--   $$
--
--   This is an open theorem statement; no formal proof is claimed. Amounts are per instalment or in pounds as appropriate; probabilities are dimensionless and discounts are to valuation.
-- source:
--   Originally derived finite-grid pension contract statement, based on the actuarial context in Chapter 11, p. 423, of Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, 3rd ed, Chapters 8–11. https://doi.org/10.1017/9781108784184 Specific benefit switches and endpoint rules are explicit new scheme assumptions, not verbatim textbook results.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_ageMixtureEventEPV
import Definitions.Def_actuarial_e_ageMixtureDatedEPV

open ActuarialDeathE

theorem actuarial_e_age_mixture_event_equals_dated (h a n e r g : ℕ) (w : ℕ → ℝ) (laws : ℕ → ℕ → ℕ → ℝ) (qualify : ℕ → ℕ → ℝ) (disc service defer retire base activeBasis deferredBasis retiredBasis increase : ℕ → ℝ) (replace : Bool) : ageMixtureEventEPV h a n e r g w laws qualify disc service defer retire base activeBasis deferredBasis retiredBasis increase replace = ageMixtureDatedEPV h a n e r g w laws qualify disc service defer retire base activeBasis deferredBasis retiredBasis increase replace := by sorry
