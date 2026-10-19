-- Prove2me | Theorems.Thm_actuarial_e_spouse_due_after_member_death
-- name    : actuarial_e_spouse_due_after_member_death
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T21:38:17.696992+00:00
-- url     : https://prove2.me/theorems/1c15f3d1-bcd9-4d95-861e-78666dc9e0ae
-- title:
--   No premature survivor payments
-- statement:
--   No premature survivor payments. The first survivor instalment is strictly later than the member's death-settlement anniversary. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   t\leq i+1\quad\Rightarrow\quad S(i,j,t)=0
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

theorem actuarial_e_spouse_due_after_member_death (i j t : ℕ) (ht : t ≤ i + 1) : spouseDue i j t = 0 := by sorry
