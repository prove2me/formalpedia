-- Prove2me | Theorems.Thm_actuarial_e_retired_death_mass_nonneg
-- name    : actuarial_e_retired_death_mass_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T19:55:16.144538+00:00
-- url     : https://prove2.me/theorems/4513d527-488e-4ab3-b7e1-0e65b087f8d7
-- title:
--   Post-retirement death probability is nonnegative
-- statement:
--   Post-retirement death probability is nonnegative. A joint mortality law assigns nonnegative mass to all retired-death cells. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   \Pr(R)\geq0
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
import Definitions.Def_actuarial_e_retiredDeathMass

open ActuarialDeathE

theorem actuarial_e_retired_death_mass_nonneg (h r : ℕ) (p : ℕ → ℕ → ℝ) (hp : validLaw h p) : 0 ≤ retiredDeathMass h r p := by sorry
