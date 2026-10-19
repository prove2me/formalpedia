-- Prove2me | Theorems.Thm_actuarial_e_member_after_death
-- name    : actuarial_e_member_after_death
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T22:49:42.796981+00:00
-- url     : https://prove2.me/theorems/58f0f34f-e0ba-4772-a7ee-de580a986d51
-- title:
--   Member pension ceases at death
-- statement:
--   Member pension ceases at death. The pension is not paid on an anniversary after member death. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   i<t\quad\Rightarrow\quad M_t(i)=0
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
import Definitions.Def_actuarial_e_memberPayment

open ActuarialDeathE

theorem actuarial_e_member_after_death (r i t : ℕ) (base : ℕ → ℝ) (hi : i < t) : memberPayment r i t base = 0 := by sorry
