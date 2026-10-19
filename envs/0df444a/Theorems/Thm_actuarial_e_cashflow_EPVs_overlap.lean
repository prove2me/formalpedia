-- Prove2me | Theorems.Thm_actuarial_e_cashflow_EPVs_overlap
-- name    : actuarial_e_cashflow_EPVs_overlap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T08:47:05.886042+00:00
-- url     : https://prove2.me/theorems/29c1dbf0-a9c8-4445-8559-4f22ea9808e5
-- title:
--   Gross versus replacement contract value
-- statement:
--   Gross versus replacement contract value. The only difference between the two complete contracts is the explicitly quantified spouse-guarantee overlap. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   V_{\text{dated}}(0)=V_{\text{dated}}(1)+V_O
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
import Definitions.Def_actuarial_e_overlapEPV
import Definitions.Def_actuarial_e_cashflowEPV

open ActuarialDeathE

theorem actuarial_e_cashflow_EPVs_overlap (h n e r g : ℕ) (p : ℕ → ℕ → ℝ) (disc service defer retire base a b c increase : ℕ → ℝ) : cashflowEPV h n e r g p disc service defer retire base a b c increase false = cashflowEPV h n e r g p disc service defer retire base a b c increase true + overlapEPV h n r g p disc c increase := by sorry
