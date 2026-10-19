-- Prove2me | Theorems.Thm_actuarial_e_deferred_revaluation_monotone
-- name    : actuarial_e_deferred_revaluation_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T22:23:14.872913+00:00
-- url     : https://prove2.me/theorems/a9bfe934-e717-432e-a7c3-a933725abd96
-- title:
--   Monotonic preserved right under revaluation
-- statement:
--   Monotonic preserved right under revaluation. Nonnegative accrued pension inherits monotonicity of the contractual growth basis. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   P_{\text{exit}}\geq0,\ G_t\leq G_u\quad\Rightarrow\quad P_D(t)\leq P_D(u)
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
import Definitions.Def_actuarial_e_revaluedDeferred

open ActuarialDeathE

theorem actuarial_e_deferred_revaluation_monotone (atExit : ℝ) (growth : ℕ → ℝ) (t u : ℕ) (hp : 0 ≤ atExit) (hu : growth t ≤ growth u) : revaluedDeferred atExit growth t ≤ revaluedDeferred atExit growth u := by sorry
