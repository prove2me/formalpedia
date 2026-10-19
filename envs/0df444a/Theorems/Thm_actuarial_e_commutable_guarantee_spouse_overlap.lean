-- Prove2me | Theorems.Thm_actuarial_e_commutable_guarantee_spouse_overlap
-- name    : actuarial_e_commutable_guarantee_spouse_overlap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T20:58:55.981749+00:00
-- url     : https://prove2.me/theorems/505c2e40-8e71-4175-8bc9-0e4d950108c5
-- title:
--   Spouse guarantee coordination is invariant to the estate's commutation election
-- statement:
--   Spouse guarantee coordination is invariant to the estate's commutation election. The parallel versus delayed spouse-pension difference is a separately priced dependent-survival stream, regardless of which mutually exclusive estate guarantee payment form was selected. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   V_{\text{parallel}}^{\kappa}=V_{\text{replacement}}^{\kappa}+O
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
import Definitions.Def_actuarial_e_qualifiedOverlapEPV
import Definitions.Def_actuarial_e_qualifiedCommutableContractEPV

open ActuarialDeathE

theorem actuarial_e_commutable_guarantee_spouse_overlap (h n e r g : ℕ) (p : ℕ → ℕ → ℝ) (q disc service defer retire base a b c increase : ℕ → ℝ) (forward : ℕ → ℕ → ℝ) (commute : Bool) : qualifiedCommutableContractEPV h n e r g p q disc service defer retire base a b c increase forward commute false = qualifiedCommutableContractEPV h n e r g p q disc service defer retire base a b c increase forward commute true + qualifiedOverlapEPV h n r g p q disc c increase := by sorry
