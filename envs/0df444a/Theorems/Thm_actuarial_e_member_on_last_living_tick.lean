-- Prove2me | Theorems.Thm_actuarial_e_member_on_last_living_tick
-- name    : actuarial_e_member_on_last_living_tick
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T22:56:35.158165+00:00
-- url     : https://prove2.me/theorems/c5a3ecfc-799c-4048-96bf-6ec62f279a20
-- title:
--   Last surviving anniversary
-- statement:
--   Last surviving anniversary. Pension payments at the end of the death-year index precede the following death settlement. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   r\leq i\quad\Rightarrow\quad M_i(i)=b_i
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

theorem actuarial_e_member_on_last_living_tick (r i : ℕ) (base : ℕ → ℝ) (hr : r ≤ i) : memberPayment r i i base = base i := by sorry
