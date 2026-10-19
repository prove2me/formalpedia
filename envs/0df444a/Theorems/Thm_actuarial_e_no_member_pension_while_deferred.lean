-- Prove2me | Theorems.Thm_actuarial_e_no_member_pension_while_deferred
-- name    : actuarial_e_no_member_pension_while_deferred
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T18:26:42.240457+00:00
-- url     : https://prove2.me/theorems/76d05f88-35f8-4793-861b-5355efea22f3
-- title:
--   Deferred death prevents retired-member payments
-- statement:
--   Deferred death prevents retired-member payments. The retirement income cannot commence after a member has already died. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   i<r\quad\Rightarrow\quad M_t(i)=0
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

theorem actuarial_e_no_member_pension_while_deferred (r i t : ℕ) (base : ℕ → ℝ) (hi : i < r) : memberPayment r i t base = 0 := by sorry
