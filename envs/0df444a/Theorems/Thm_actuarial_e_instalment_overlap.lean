-- Prove2me | Theorems.Thm_actuarial_e_instalment_overlap
-- name    : actuarial_e_instalment_overlap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T08:32:24.930144+00:00
-- url     : https://prove2.me/theorems/89de7e2d-3d9c-4885-939f-ada9c6108f02
-- title:
--   Combined instalment overlap reconciliation
-- statement:
--   Combined instalment overlap reconciliation. Member and guarantee streams are unchanged; only the spouse rider distinguishes the two contracts. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   C_t(i,j;0)=C_t(i,j;1)+O_t(i,j)
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
import Definitions.Def_actuarial_e_overlapPayment
import Definitions.Def_actuarial_e_instalment

open ActuarialDeathE

theorem actuarial_e_instalment_overlap (h e r g i j t : ℕ) (base a b c increase : ℕ → ℝ) : instalment h e r g i j t base a b c increase false = instalment h e r g i j t base a b c increase true + overlapPayment h r g i j t c increase := by sorry
