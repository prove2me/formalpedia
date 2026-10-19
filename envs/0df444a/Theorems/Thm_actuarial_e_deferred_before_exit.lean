-- Prove2me | Theorems.Thm_actuarial_e_deferred_before_exit
-- name    : actuarial_e_deferred_before_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T17:44:15.021975+00:00
-- url     : https://prove2.me/theorems/e563a567-2ed2-479f-b475-a06c00509e83
-- title:
--   No deferred benefit while active
-- statement:
--   No deferred benefit while active. A member who has not exited cannot simultaneously trigger the deferred death regime. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   i<e\quad\Rightarrow\quad I_D(i)=0
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

theorem actuarial_e_deferred_before_exit (h e r i : ℕ) (hi : i < e) : deferred h e r i = 0 := by sorry
