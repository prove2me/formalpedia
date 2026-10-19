-- Prove2me | Theorems.Thm_actuarial_e_child_EPVs_zero_horizon
-- name    : actuarial_e_child_EPVs_zero_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T20:41:50.496968+00:00
-- url     : https://prove2.me/theorems/b75a9b12-c0d0-48da-871e-8953094d560f
-- title:
--   No child instalments in an empty payment horizon
-- statement:
--   No child instalments in an empty payment horizon. A zero length pension schedule has no age-limited child pension despite nonzero potential member-death probability. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   n=0\ \Rightarrow\ V_{\text{child,event}}=0
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

theorem actuarial_e_child_EPVs_zero_horizon (h childAge maximumAge : ℕ) (p : ℕ → ℕ → ℝ) (disc basis increase : ℕ → ℝ) : childEventEPV h 0 childAge maximumAge p disc basis increase = 0 := by sorry
