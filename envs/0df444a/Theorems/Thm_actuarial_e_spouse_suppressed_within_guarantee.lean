-- Prove2me | Theorems.Thm_actuarial_e_spouse_suppressed_within_guarantee
-- name    : actuarial_e_spouse_suppressed_within_guarantee
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-17T19:09:31.594302+00:00
-- url     : https://prove2.me/theorems/9514a449-df94-423b-bb8d-2bbd6a03ab72
-- title:
--   Replacing the guarantee suppresses overlapping spouse payments
-- statement:
--   Replacing the guarantee suppresses overlapping spouse payments. In a replacement contract the survivor pension is not paid over the remaining guarantee period. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   r\leq i,\ t<r+g,\ e\leq r\quad\Rightarrow\quad R_t(i,j;1)=0
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

theorem actuarial_e_spouse_suppressed_within_guarantee (h e r g i j t : ℕ) (a b c increase : ℕ → ℝ) (her : e ≤ r) (hi : r ≤ i) (ht : t < r + g) : spousePayment h e r g i j t a b c increase true = 0 := by sorry
