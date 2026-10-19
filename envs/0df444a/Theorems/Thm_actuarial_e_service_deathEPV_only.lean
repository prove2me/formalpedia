-- Prove2me | Theorems.Thm_actuarial_e_service_deathEPV_only
-- name    : actuarial_e_service_deathEPV_only
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T11:01:12.45836+00:00
-- url     : https://prove2.me/theorems/b5110105-855c-49a7-9abf-7edf20d8ecd6
-- title:
--   Salary-related service death claim priced by genuine death event
-- statement:
--   Salary-related service death claim priced by genuine death event. Payment arises precisely in active-service death cells and never in other member states. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   V_L(L_D=0,L_R=0)=\mathbb{E}_p\bigl[v_{i+1}I_A(i)L_A(i+1)\bigr]
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
import Definitions.Def_actuarial_e_expect
import Definitions.Def_actuarial_e_active
import Definitions.Def_actuarial_e_deathEPV

open ActuarialDeathE

theorem actuarial_e_service_deathEPV_only (h e r : ℕ) (p : ℕ → ℕ → ℝ) (disc service : ℕ → ℝ) : deathEPV h e r p disc service (fun t => 0) (fun t => 0) = expect h p (fun i j => disc (i + 1) * active h e i * service (i + 1)) := by sorry
