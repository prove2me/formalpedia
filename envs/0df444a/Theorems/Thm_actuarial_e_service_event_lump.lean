-- Prove2me | Theorems.Thm_actuarial_e_service_event_lump
-- name    : actuarial_e_service_event_lump
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T22:23:35.459552+00:00
-- url     : https://prove2.me/theorems/bdbaf87e-34c8-439d-af8b-c2829e3b8300
-- title:
--   Active death-event lump valuation
-- statement:
--   Active death-event lump valuation. Death in active employment uses only the service-specific schedule at settlement. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   i<e,\ i<h,\ e\leq r\quad\Rightarrow\quad L(i)=L_A(i+1)
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

open ActuarialDeathE

theorem actuarial_e_service_event_lump (h e r i : ℕ) (service defer retire : ℕ → ℝ) (her : e ≤ r) (hi : i < h) (he : i < e) : regimeLump h e r i service defer retire = service (i + 1) := by sorry
