-- Prove2me | Theorems.Thm_actuarial_e_child_EPVs_add_benefits
-- name    : actuarial_e_child_EPVs_add_benefits
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T20:44:47.310652+00:00
-- url     : https://prove2.me/theorems/5b7ecf47-6537-47c8-8645-51e67ccf3576
-- title:
--   Child pensions from distinct tranches sum without mixing increases
-- statement:
--   Child pensions from distinct tranches sum without mixing increases. Additivity holds when the tranches share a survivor indexation basis; different increases remain in separately computed streams. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   V_{\text{child}}(b_1+b_2)=V_{\text{child}}(b_1)+V_{\text{child}}(b_2)
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
import Definitions.Def_actuarial_e_childEventEPV

open ActuarialDeathE

theorem actuarial_e_child_EPVs_add_benefits (h n childAge maximumAge : ℕ) (p : ℕ → ℕ → ℝ) (disc b1 b2 increase : ℕ → ℝ) : childEventEPV h n childAge maximumAge p disc (fun t => b1 t + b2 t) increase = childEventEPV h n childAge maximumAge p disc b1 increase + childEventEPV h n childAge maximumAge p disc b2 increase := by sorry
