-- Prove2me | Theorems.Thm_actuarial_e_spouse_overlap_path
-- name    : actuarial_e_spouse_overlap_path
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-17T19:10:16.606046+00:00
-- url     : https://prove2.me/theorems/fb739066-075f-4694-8e48-b6de8d36a546
-- title:
--   Pointwise spouse-guarantee overlap reconciliation
-- statement:
--   Pointwise spouse-guarantee overlap reconciliation. The gross spouse pension is exactly the replacement pension plus the instalment suppressed by the guarantee switch. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   R_t(i,j;0)=R_t(i,j;1)+O_t(i,j)
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
import Definitions.Def_actuarial_e_overlapPayment

open ActuarialDeathE

theorem actuarial_e_spouse_overlap_path (h e r g i j t : ℕ) (a b c increase : ℕ → ℝ) : spousePayment h e r g i j t a b c increase false = spousePayment h e r g i j t a b c increase true + overlapPayment h r g i j t c increase := by sorry
