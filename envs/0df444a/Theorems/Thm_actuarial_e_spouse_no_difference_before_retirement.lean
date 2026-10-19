-- Prove2me | Theorems.Thm_actuarial_e_spouse_no_difference_before_retirement
-- name    : actuarial_e_spouse_no_difference_before_retirement
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-17T05:31:05.664165+00:00
-- url     : https://prove2.me/theorems/d15e9a30-4f9f-4df5-b92e-020d495e7d17
-- title:
--   Guarantee coordination affects retired deaths only
-- statement:
--   Guarantee coordination affects retired deaths only. Service and deferred survivor pensions are not offset by a guarantee that has not commenced. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   i<r\quad\Rightarrow\quad R_t(i,j;0)=R_t(i,j;1)
--   $$
--
--   This is an open theorem statement; no formal proof is claimed. Amounts are per instalment or in pounds as appropriate; probabilities are dimensionless and discounts are to valuation.
-- source:
--   Originally derived finite-grid pension contract statement, based on the actuarial context in Chapter 10, p. 388, of Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, 3rd ed, Chapters 8–11. https://doi.org/10.1017/9781108784184 Specific benefit switches and endpoint rules are explicit new scheme assumptions, not verbatim textbook results.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_spousePayment

open ActuarialDeathE

theorem actuarial_e_spouse_no_difference_before_retirement (h e r g i j t : ℕ) (a b c increase : ℕ → ℝ) (hi : i < r) : spousePayment h e r g i j t a b c increase false = spousePayment h e r g i j t a b c increase true := by sorry
