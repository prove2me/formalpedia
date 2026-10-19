-- Prove2me | Theorems.Thm_actuarial_e_baseline_contract_equivalence
-- name    : actuarial_e_baseline_contract_equivalence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T20:04:10.051783+00:00
-- url     : https://prove2.me/theorems/ad568249-672f-4d05-a22d-1e9f9765befb
-- title:
--   Fixed-spouse core contract valuation equivalence
-- statement:
--   Fixed-spouse core contract valuation equivalence. A finite joint mortality law reconciles the unweighted contract's death, member, survivor and guaranteed payment streams. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   V_{\text{event}}(1,\eta)=V_{\text{dated}}(1,\eta),\quad V_{\text{event}}(1,0)=V_{\text{event}}(1,1)+V_O(1)
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
import Definitions.Def_actuarial_e_validLaw
import Definitions.Def_actuarial_e_contractEPV
import Definitions.Def_actuarial_e_overlapEPV
import Definitions.Def_actuarial_e_cashflowEPV

open ActuarialDeathE

theorem actuarial_e_baseline_contract_equivalence (h n e r g : ℕ) (p : ℕ → ℕ → ℝ) (disc service defer retire base a b c increase : ℕ → ℝ) (replace : Bool) (hExit : e ≤ r) (hRet : r ≤ h) (hLaw : validLaw h p) : (contractEPV h n e r g p disc service defer retire base a b c increase replace = cashflowEPV h n e r g p disc service defer retire base a b c increase replace) ∧ (contractEPV h n e r g p disc service defer retire base a b c increase false = contractEPV h n e r g p disc service defer retire base a b c increase true + overlapEPV h n r g p disc c increase) := by sorry
