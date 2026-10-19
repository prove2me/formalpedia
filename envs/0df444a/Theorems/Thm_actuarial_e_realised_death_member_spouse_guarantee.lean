-- Prove2me | Theorems.Thm_actuarial_e_realised_death_member_spouse_guarantee
-- name    : actuarial_e_realised_death_member_spouse_guarantee
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T08:46:26.762669+00:00
-- url     : https://prove2.me/theorems/e4ed7cc3-a53a-4a7f-8b81-d21c1f3ceb52
-- title:
--   Pathwise decomposition by payment recipient
-- statement:
--   Pathwise decomposition by payment recipient. Realised claims contain distinct death settlement, member instalment, qualifying spouse instalment and estate-guarantee payment streams. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   Z(i,j;\eta)=v_{i+1}L(i)+\sum_t v_t\bigl(M_t+R_t(\eta)+G_t\bigr)
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
import Definitions.Def_actuarial_e_deathPV
import Definitions.Def_actuarial_e_memberPayment
import Definitions.Def_actuarial_e_guaranteePayment
import Definitions.Def_actuarial_e_spousePayment
import Definitions.Def_actuarial_e_realisedPV

open ActuarialDeathE

theorem actuarial_e_realised_death_member_spouse_guarantee (h n e r g i j : ℕ) (disc service defer retire base a b c increase : ℕ → ℝ) (replace : Bool) : realisedPV h n e r g i j disc service defer retire base a b c increase replace = deathPV h e r i disc service defer retire + ∑ t ∈ Finset.range n, disc t * (memberPayment r i t base + spousePayment h e r g i j t a b c increase replace + guaranteePayment h r g i t base) := by sorry
