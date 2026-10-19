-- Prove2me | Theorems.Thm_actuarial_e_guarantee_capital_pre_retirement
-- name    : actuarial_e_guarantee_capital_pre_retirement
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T20:55:41.856688+00:00
-- url     : https://prove2.me/theorems/f3720a51-3f78-4482-8167-b6e08d27d08e
-- title:
--   Death before retirement carries no commenced estate guarantee
-- statement:
--   Death before retirement carries no commenced estate guarantee. The option cannot create a cash payment for an active or deferred death where no retirement guarantee has commenced. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   i<r\Rightarrow K_{i+1}=0
--   $$
--
--   This is an open theorem statement; no formal proof is claimed. Amounts are per instalment or in pounds as appropriate; probabilities are dimensionless and discounts are to valuation.
-- source:
--   Originally derived finite-grid pension contract statement, based on the actuarial context in Chapter 10, p. 388, of Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, 3rd ed, Chapters 8–11. https://doi.org/10.1017/9781108784184 Specific benefit switches and endpoint rules are explicit new scheme assumptions, not verbatim textbook results.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_guaranteeCapitalAtDeath

open ActuarialDeathE

theorem actuarial_e_guarantee_capital_pre_retirement (n h r g i : ℕ) (forward : ℕ → ℕ → ℝ) (base : ℕ → ℝ) (hi : i < r) : guaranteeCapitalAtDeath n h r g i forward base = 0 := by sorry
