-- Prove2me | Theorems.Thm_actuarial_e_deathPV_zero_rate
-- name    : actuarial_e_deathPV_zero_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T22:41:45.090001+00:00
-- url     : https://prove2.me/theorems/a69fa4a9-6c04-4ed3-8009-dc7c53f2df5c
-- title:
--   Death lump under zero-interest discounting
-- statement:
--   Death lump under zero-interest discounting. A unit discount curve leaves the settlement amount undiscounted. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   v_t=1\quad\Rightarrow\quad Z_L(i)=L(i)
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
import Definitions.Def_actuarial_e_regimeLump
import Definitions.Def_actuarial_e_deathPV

open ActuarialDeathE

theorem actuarial_e_deathPV_zero_rate (h e r i : ℕ) (service defer retire : ℕ → ℝ) : deathPV h e r i (fun t => (1 : ℝ)) service defer retire = regimeLump h e r i service defer retire := by sorry
