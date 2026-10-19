-- Prove2me | Theorems.Thm_actuarial_e_active_after_exit
-- name    : actuarial_e_active_after_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T17:44:05.318136+00:00
-- url     : https://prove2.me/theorems/4e9f7834-0d2f-40b7-bcd1-380bab46ecfa
-- title:
--   Active eligibility ends at exit
-- statement:
--   Active eligibility ends at exit. An individual already past the exit anniversary cannot generate a salary-multiple death-in-service claim. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   e\leq i\quad\Rightarrow\quad I_A(i)=0
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
import Definitions.Def_actuarial_e_active

open ActuarialDeathE

theorem actuarial_e_active_after_exit (h e i : ℕ) (hi : e ≤ i) : active h e i = 0 := by sorry
