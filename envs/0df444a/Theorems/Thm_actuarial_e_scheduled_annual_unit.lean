-- Prove2me | Theorems.Thm_actuarial_e_scheduled_annual_unit
-- name    : actuarial_e_scheduled_annual_unit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T08:32:48.86004+00:00
-- url     : https://prove2.me/theorems/b5260869-bcf2-4b22-a628-52f802209c92
-- title:
--   Annual tick selection
-- statement:
--   Annual tick selection. Every integer tick is selected if the period unit is one year. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   H_1(t)=1
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
import Definitions.Def_actuarial_e_scheduled

open ActuarialDeathE

theorem actuarial_e_scheduled_annual_unit (t : ℕ) : scheduled 1 t = 1 := by sorry
