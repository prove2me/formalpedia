-- Prove2me | Theorems.Thm_actuarial_e_spouse_due_after_both_conditions
-- name    : actuarial_e_spouse_due_after_both_conditions
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T21:38:38.619809+00:00
-- url     : https://prove2.me/theorems/048a1ec6-30d5-4160-88cd-4b184d1be269
-- title:
--   Positive qualifying survivor state
-- statement:
--   Positive qualifying survivor state. A survivor instalment follows member death and is payable when the qualifying spouse lives on its due date. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   i+1<t\leq j\quad\Rightarrow\quad S(i,j,t)=1
--   $$
--
--   This is an open theorem statement; no formal proof is claimed. Amounts are per instalment or in pounds as appropriate; probabilities are dimensionless and discounts are to valuation.
-- source:
--   Originally derived finite-grid pension contract statement, based on the actuarial context in Chapter 9, p. 359, of Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, 3rd ed, Chapters 8–11. https://doi.org/10.1017/9781108784184 Specific benefit switches and endpoint rules are explicit new scheme assumptions, not verbatim textbook results.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_spouseDue

open ActuarialDeathE

theorem actuarial_e_spouse_due_after_both_conditions (i j t : ℕ) (hi : i + 1 < t) (hj : t ≤ j) : spouseDue i j t = 1 := by sorry
