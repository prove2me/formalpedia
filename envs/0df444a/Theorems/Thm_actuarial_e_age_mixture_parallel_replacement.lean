-- Prove2me | Theorems.Thm_actuarial_e_age_mixture_parallel_replacement
-- name    : actuarial_e_age_mixture_parallel_replacement
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T20:19:55.415291+00:00
-- url     : https://prove2.me/theorems/dae108b3-78e7-4947-ab0b-f9343ddb7fbc
-- title:
--   Mixed spouse-age distribution guarantees are reconciled without double counting
-- statement:
--   Mixed spouse-age distribution guarantees are reconciled without double counting. The suppression correction is averaged across all possible qualifying-dependent age differences with its own mortality and survivor basis. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   V_{\text{parallel}}^{\text{mix}}=V_{\text{replacement}}^{\text{mix}}+O^{\text{mix}}
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
import Definitions.Def_actuarial_e_ageMixtureOverlapEPV

open ActuarialDeathE

theorem actuarial_e_age_mixture_parallel_replacement (h a n e r g : ℕ) (w : ℕ → ℝ) (laws : ℕ → ℕ → ℕ → ℝ) (qualify : ℕ → ℕ → ℝ) (disc service defer retire base activeBasis deferredBasis retiredBasis increase : ℕ → ℝ) : ageMixtureEventEPV h a n e r g w laws qualify disc service defer retire base activeBasis deferredBasis retiredBasis increase false = ageMixtureEventEPV h a n e r g w laws qualify disc service defer retire base activeBasis deferredBasis retiredBasis increase true + ageMixtureOverlapEPV h a n r g w laws qualify disc retiredBasis increase := by sorry
