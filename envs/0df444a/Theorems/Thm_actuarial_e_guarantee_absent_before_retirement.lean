-- Prove2me | Theorems.Thm_actuarial_e_guarantee_absent_before_retirement
-- name    : actuarial_e_guarantee_absent_before_retirement
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-17T04:58:15.583539+00:00
-- url     : https://prove2.me/theorems/1d015029-eeff-4b3a-b227-a64b00f9714c
-- title:
--   Death before pension commencement excludes guarantee
-- statement:
--   Death before pension commencement excludes guarantee. The pension payment guarantee arises only for commenced retirement pensions. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   i<r\quad\Rightarrow\quad G_t(i)=0
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

theorem actuarial_e_guarantee_absent_before_retirement (h r g i t : ℕ) (base : ℕ → ℝ) (hi : i < r) : guaranteePayment h r g i t base = 0 := by sorry
