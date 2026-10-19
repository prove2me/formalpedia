-- Prove2me | Theorems.Thm_actuarial_e_immediate_deferred_spouse_difference
-- name    : actuarial_e_immediate_deferred_spouse_difference
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T19:56:32.649163+00:00
-- url     : https://prove2.me/theorems/0aac129c-1b04-488a-96fe-06ed52d9abdb
-- title:
--   Immediate versus deferred spouse annuity due-date difference
-- statement:
--   Immediate versus deferred spouse annuity due-date difference. The precise difference is the first eligible payment at the member's death settlement tick. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   S_{\text{immediate}}(i,j,t)=S(i,j,t)+\mathbf{1}_{\{i<j,\ t=i+1\}}
--   $$
--
--   This is an open theorem statement; no formal proof is claimed. Amounts are per instalment or in pounds as appropriate; probabilities are dimensionless and discounts are to valuation.
-- source:
--   Originally derived finite-grid pension contract statement, based on the actuarial context in Chapter 10, p. 388, of Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, 3rd ed, Chapters 8–11. https://doi.org/10.1017/9781108784184 Specific benefit switches and endpoint rules are explicit new scheme assumptions, not verbatim textbook results.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_spouseDue
import Definitions.Def_actuarial_e_spouseDueImmediate

open ActuarialDeathE

theorem actuarial_e_immediate_deferred_spouse_difference (i j t : ℕ) : spouseDueImmediate i j t = spouseDue i j t + (if i < j ∧ t = i + 1 then (1 : ℝ) else 0) := by sorry
