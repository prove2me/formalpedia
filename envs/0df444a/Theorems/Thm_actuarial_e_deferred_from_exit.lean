-- Prove2me | Theorems.Thm_actuarial_e_deferred_from_exit
-- name    : actuarial_e_deferred_from_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T17:44:59.151317+00:00
-- url     : https://prove2.me/theorems/ead81df3-e3ec-46bb-99e2-7d6e20d856f7
-- title:
--   Preserved entitlement after exit
-- statement:
--   Preserved entitlement after exit. A deferred death is recognised immediately after the exit boundary and before retirement. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   e\leq i<r,\ i<h\quad\Rightarrow\quad I_D(i)=1
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
import Definitions.Def_actuarial_e_deferred

open ActuarialDeathE

theorem actuarial_e_deferred_from_exit (h e r i : ℕ) (hi : i < h) (hx : e ≤ i) (hr : i < r) : deferred h e r i = 1 := by sorry
