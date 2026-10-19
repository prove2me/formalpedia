-- Prove2me | Theorems.Thm_actuarial_e_member_on_commencement
-- name    : actuarial_e_member_on_commencement
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T22:56:16.893002+00:00
-- url     : https://prove2.me/theorems/d89ff4bf-fa5e-4ec1-87cf-df6dba32a4b8
-- title:
--   First pension instalment
-- statement:
--   First pension instalment. Payment on commencement is due only if the member survives that anniversary. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   r\leq i\quad\Rightarrow\quad M_r(i)=b_r
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

theorem actuarial_e_member_on_commencement (r i : ℕ) (base : ℕ → ℝ) (hr : r ≤ i) : memberPayment r i r base = base r := by sorry
