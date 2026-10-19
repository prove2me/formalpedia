-- Prove2me | Theorems.Thm_actuarial_e_age_mixture_add_scenario
-- name    : actuarial_e_age_mixture_add_scenario
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T20:28:35.151272+00:00
-- url     : https://prove2.me/theorems/f6f9b42b-e673-47a6-a022-9e10377407ea
-- title:
--   Adding an age-difference scenario changes EPV by its weighted valuation
-- statement:
--   Adding an age-difference scenario changes EPV by its weighted valuation. The marginal scenario contribution remains a separately priced, death-fixed-eligibility pension contract. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   V_{a+1}=V_a+w_aV^{(a)}
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
import Definitions.Def_actuarial_e_qualifiedContractEPV
import Definitions.Def_actuarial_e_ageMixtureEventEPV

open ActuarialDeathE

theorem actuarial_e_age_mixture_add_scenario (h a n e r g : ℕ) (w : ℕ → ℝ) (laws : ℕ → ℕ → ℕ → ℝ) (qualify : ℕ → ℕ → ℝ) (disc service defer retire base activeBasis deferredBasis retiredBasis increase : ℕ → ℝ) (replace : Bool) : ageMixtureEventEPV h (a + 1) n e r g w laws qualify disc service defer retire base activeBasis deferredBasis retiredBasis increase replace = ageMixtureEventEPV h a n e r g w laws qualify disc service defer retire base activeBasis deferredBasis retiredBasis increase replace + w a * qualifiedContractEPV h n e r g (laws a) (qualify a) disc service defer retire base activeBasis deferredBasis retiredBasis increase replace := by sorry
