-- Prove2me | Theorems.Thm_actuarial_e_guarantee_endpoint
-- name    : actuarial_e_guarantee_endpoint
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-17T04:58:29.441513+00:00
-- url     : https://prove2.me/theorems/44ece067-3518-4960-9296-a6b4ddfc7ed6
-- title:
--   Exclusive guarantee endpoint
-- statement:
--   Exclusive guarantee endpoint. The first anniversary outside the guaranteed term attracts no continuing estate payment. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   G_{r+g}(i)=0
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
import Definitions.Def_actuarial_e_guaranteePayment

open ActuarialDeathE

theorem actuarial_e_guarantee_endpoint (h r g i : ℕ) (base : ℕ → ℝ) : guaranteePayment h r g i (r + g) base = 0 := by sorry
