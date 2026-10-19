-- Prove2me | Theorems.Thm_actuarial_e_child_due_if_predeceased
-- name    : actuarial_e_child_due_if_predeceased
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T20:29:21.59799+00:00
-- url     : https://prove2.me/theorems/a7f07d8f-1b3b-4a55-9e8b-ab992be9b941
-- title:
--   Predeceased child cannot receive continuation pension
-- statement:
--   Predeceased child cannot receive continuation pension. The age rule does not create benefits for an already-deceased potential dependant. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   j\leq i\ \Rightarrow\ C_{\text{child}}=0
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
import Definitions.Def_actuarial_e_childDue

open ActuarialDeathE

theorem actuarial_e_child_due_if_predeceased (i j t childAge maximumAge : ℕ) (hj : j ≤ i) : childDue i j t childAge maximumAge = 0 := by sorry
