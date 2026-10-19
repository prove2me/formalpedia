-- Prove2me | Theorems.Thm_actuarial_e_deathEPV_disjoint_sum
-- name    : actuarial_e_deathEPV_disjoint_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T18:26:33.383295+00:00
-- url     : https://prove2.me/theorems/94fa5c2f-b254-4a75-a9ab-89031635cc82
-- title:
--   Additivity of mutually exclusive death lumps
-- statement:
--   Additivity of mutually exclusive death lumps. Three death regimes are disjoint for each individual outcome and remain additive in expectation. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   V_L=V_L^{(\text{active})}+V_L^{(\text{deferred})}+V_L^{(\text{retired})}
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
import Definitions.Def_actuarial_e_deathEPV

open ActuarialDeathE

theorem actuarial_e_deathEPV_disjoint_sum (h e r : ℕ) (p : ℕ → ℕ → ℝ) (disc service defer retire : ℕ → ℝ) : deathEPV h e r p disc service defer retire = deathEPV h e r p disc service (fun t => 0) (fun t => 0) + deathEPV h e r p disc (fun t => 0) defer (fun t => 0) + deathEPV h e r p disc (fun t => 0) (fun t => 0) retire := by sorry
