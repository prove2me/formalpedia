-- Prove2me | Theorems.Thm_actuarial_e_two_tranche_additive
-- name    : actuarial_e_two_tranche_additive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T08:40:53.316576+00:00
-- url     : https://prove2.me/theorems/dd72ece5-47df-4cc5-9a20-864aaa43a957
-- title:
--   Two distinct tranches have additive scheduled payments
-- statement:
--   Two distinct tranches have additive scheduled payments. Separate survivor-indexation assumptions are retained through the monetary sum. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   C^{(1,2)}_t=C^{(1)}_t+C^{(2)}_t
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
import Definitions.Def_actuarial_e_instalment
import Definitions.Def_actuarial_e_tranchePayment

open ActuarialDeathE

theorem actuarial_e_two_tranche_additive (h e r g i j t : ℕ) (base1 base2 a1 a2 b1 b2 c1 c2 inc1 inc2 : ℕ → ℝ) (replace : Bool) : tranchePayment h e r g i j t base1 base2 a1 a2 b1 b2 c1 c2 inc1 inc2 replace = instalment h e r g i j t base1 a1 b1 c1 inc1 replace + instalment h e r g i j t base2 a2 b2 c2 inc2 replace := by sorry
