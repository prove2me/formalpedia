-- Prove2me | Theorems.Thm_actuarial_e_deferred_death_mass_nonneg
-- name    : actuarial_e_deferred_death_mass_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T18:29:43.340345+00:00
-- url     : https://prove2.me/theorems/d9081077-3cca-41fd-b0dc-f7154500cff7
-- title:
--   Preserved-rights death probability is nonnegative
-- statement:
--   Preserved-rights death probability is nonnegative. Nonnegative individual event probabilities follow from genuine joint mortality mass and the deferred-state filter. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   \Pr(D)\geq0
--   $$
--
--   This is an open theorem statement; no formal proof is claimed. Amounts are per instalment or in pounds as appropriate; probabilities are dimensionless and discounts are to valuation.
-- source:
--   Originally derived finite-grid pension contract statement, based on the actuarial context in Chapter 9, p. 359, of Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, 3rd ed, Chapters 8–11. https://doi.org/10.1017/9781108784184 Specific benefit switches and endpoint rules are explicit new scheme assumptions, not verbatim textbook results.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_validLaw
import Definitions.Def_actuarial_e_deferredDeathMass

open ActuarialDeathE

theorem actuarial_e_deferred_death_mass_nonneg (h e r : ℕ) (p : ℕ → ℕ → ℝ) (hp : validLaw h p) : 0 ≤ deferredDeathMass h e r p := by sorry
