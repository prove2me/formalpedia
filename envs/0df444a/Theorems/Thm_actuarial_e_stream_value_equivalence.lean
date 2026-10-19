-- Prove2me | Theorems.Thm_actuarial_e_stream_value_equivalence
-- name    : actuarial_e_stream_value_equivalence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T09:02:44.687755+00:00
-- url     : https://prove2.me/theorems/70012bfd-d793-4499-89d8-77488c5a0762
-- title:
--   Event-based equals payment-date EPV
-- statement:
--   Event-based equals payment-date EPV. Fubini over a finite joint mortality law reconciles a death-event model with distinct dated cashflow streams. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   V_{\text{event}}(\eta)=V_{\text{dated}}(\eta)
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
import Definitions.Def_actuarial_e_contractEPV
import Definitions.Def_actuarial_e_cashflowEPV

open ActuarialDeathE

theorem actuarial_e_stream_value_equivalence (h n e r g : ℕ) (p : ℕ → ℕ → ℝ) (disc service defer retire base a b c increase : ℕ → ℝ) (replace : Bool) : contractEPV h n e r g p disc service defer retire base a b c increase replace = cashflowEPV h n e r g p disc service defer retire base a b c increase replace := by sorry
