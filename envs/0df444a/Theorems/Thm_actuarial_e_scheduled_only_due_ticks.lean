-- Prove2me | Theorems.Thm_actuarial_e_scheduled_only_due_ticks
-- name    : actuarial_e_scheduled_only_due_ticks
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T08:32:59.584574+00:00
-- url     : https://prove2.me/theorems/d0e417f1-8578-4c78-aaa7-c9060afc183e
-- title:
--   Positive scheduled payment grid
-- statement:
--   Positive scheduled payment grid. Changing the clock from years to months preserves contractual due dates when period spacing is consistently scaled. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   m>0,\ t\bmod m=0\quad\Rightarrow\quad H_m(t)=1
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
import Definitions.Def_actuarial_e_scheduled

open ActuarialDeathE

theorem actuarial_e_scheduled_only_due_ticks (m t : ℕ) (hm : 0 < m) (ht : t % m = 0) : scheduled m t = 1 := by sorry
