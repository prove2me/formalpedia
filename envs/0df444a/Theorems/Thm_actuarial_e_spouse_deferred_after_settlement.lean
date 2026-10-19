-- Prove2me | Theorems.Thm_actuarial_e_spouse_deferred_after_settlement
-- name    : actuarial_e_spouse_deferred_after_settlement
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T19:55:37.873532+00:00
-- url     : https://prove2.me/theorems/cac8e4f7-7334-4863-815f-85b336d71bdd
-- title:
--   Deferred survivor pension starts after settlement
-- statement:
--   Deferred survivor pension starts after settlement. The contract's later-start option pays strictly after the member death-settlement anniversary. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   S(i,j,i+1)=0
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
import Definitions.Def_actuarial_e_spouseDue

open ActuarialDeathE

theorem actuarial_e_spouse_deferred_after_settlement (i j : ℕ) : spouseDue i j (i + 1) = 0 := by sorry
