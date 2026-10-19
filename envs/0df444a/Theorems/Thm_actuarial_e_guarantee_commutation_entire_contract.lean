-- Prove2me | Theorems.Thm_actuarial_e_guarantee_commutation_entire_contract
-- name    : actuarial_e_guarantee_commutation_entire_contract
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T20:57:31.037361+00:00
-- url     : https://prove2.me/theorems/53959faa-1005-4e45-a974-2e32eb995278
-- title:
--   Full pension EPV invariant under coherent estate guarantee commutation
-- statement:
--   Full pension EPV invariant under coherent estate guarantee commutation. The member's death benefit, qualifying spouse pension and original member annuity retain their values while the estate receives a financially equivalent selected guarantee form. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   v_t=v_{i+1}f_{i+1,t}\Rightarrow V_{\text{total}}^{\kappa}=V_{\text{total}}^{0}
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
import Definitions.Def_actuarial_e_qualifiedContractEPV
import Definitions.Def_actuarial_e_qualifiedCommutableContractEPV

open ActuarialDeathE

theorem actuarial_e_guarantee_commutation_entire_contract (h n e r g : ℕ) (p : ℕ → ℕ → ℝ) (q disc service defer retire base a b c increase : ℕ → ℝ) (forward : ℕ → ℕ → ℝ) (commute replace : Bool) (hf : ∀ i ∈ Finset.range (h + 1), ∀ t ∈ Finset.range n, disc t = disc (i + 1) * forward (i + 1) t) : qualifiedCommutableContractEPV h n e r g p q disc service defer retire base a b c increase forward commute replace = qualifiedContractEPV h n e r g p q disc service defer retire base a b c increase replace := by sorry
