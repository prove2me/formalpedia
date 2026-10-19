-- Prove2me | Theorems.Thm_actuarial_e_root_contract_equivalence
-- name    : actuarial_e_root_contract_equivalence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T20:59:18.302041+00:00
-- url     : https://prove2.me/theorems/72475b6b-fd97-4026-9c4d-1bafe076da45
-- title:
--   Complete death-event pension value, spouse qualification and guarantee adjustment
-- statement:
--   Complete death-event pension value, spouse qualification and guarantee adjustment. Under a proper joint life law and frozen qualification chance at member death, a switched salary-related active lump, revalued deferred death benefit, retirement rider, spouse pension and estate guarantee have the same event and dated values. The separately priced suppressed overlap reconciles parallel and replacement contracts. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   V_{\text{event}}^{\text{rules}}(q,\eta)=V_{\text{dated}}^{\text{rules}}(q,\eta),\quad V_{\text{event}}^{\text{rules}}(q,0)=V_{\text{event}}^{\text{rules}}(q,1)+V_O(q)
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
import Definitions.Def_actuarial_e_qualifiedOverlapEPV
import Definitions.Def_actuarial_e_qualifiedEventFromRules
import Definitions.Def_actuarial_e_qualifiedDatedFromRules

open ActuarialDeathE

theorem actuarial_e_root_contract_equivalence (h n e r g : ℕ) (p : ℕ → ℕ → ℝ) (q : ℕ → ℝ) (k atExit : ℝ) (salary accrued contributions growth capitalFactor refunds retire base a b c increase disc : ℕ → ℝ) (paySalary payAccrued serviceRefund deferRefund replace : Bool) (hExit : e ≤ r) (hRet : r ≤ h) (hProjection : n ≤ h + 1) (hLaw : validLaw h p) (hQ : ∀ i ∈ Finset.range (h + 1), 0 ≤ q i ∧ q i ≤ 1) : (qualifiedEventFromRules h n e r g p q k atExit salary accrued contributions growth capitalFactor refunds retire base a b c increase disc paySalary payAccrued serviceRefund deferRefund replace = qualifiedDatedFromRules h n e r g p q k atExit salary accrued contributions growth capitalFactor refunds retire base a b c increase disc paySalary payAccrued serviceRefund deferRefund replace) ∧ (qualifiedEventFromRules h n e r g p q k atExit salary accrued contributions growth capitalFactor refunds retire base a b c increase disc paySalary payAccrued serviceRefund deferRefund false = qualifiedEventFromRules h n e r g p q k atExit salary accrued contributions growth capitalFactor refunds retire base a b c increase disc paySalary payAccrued serviceRefund deferRefund true + qualifiedOverlapEPV h n r g p q disc c increase) := by sorry
