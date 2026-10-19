-- Prove2me | Theorems.Thm_actuarial_e_revaluation_at_exit
-- name    : actuarial_e_revaluation_at_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T22:22:32.548382+00:00
-- url     : https://prove2.me/theorems/0f1c70d6-1625-453d-8df1-0932fe290b0a
-- title:
--   Revaluation at the preservation base date
-- statement:
--   Revaluation at the preservation base date. A unit growth factor preserves the vested nominal benefit at the original exit value. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   G_t=1\quad\Rightarrow\quad P_{\text{exit}}G_t=P_{\text{exit}}
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

theorem actuarial_e_revaluation_at_exit (atExit : ℝ) (growth : ℕ → ℝ) (t : ℕ) (h : growth t = 1) : revaluedDeferred atExit growth t = atExit := by sorry
