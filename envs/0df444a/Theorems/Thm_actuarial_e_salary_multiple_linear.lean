-- Prove2me | Theorems.Thm_actuarial_e_salary_multiple_linear
-- name    : actuarial_e_salary_multiple_linear
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T21:52:52.174102+00:00
-- url     : https://prove2.me/theorems/d729cc30-4bbc-4e4f-9c40-37056f29305f
-- title:
--   Salary-multiple scaling
-- statement:
--   Salary-multiple scaling. The death-in-service salary multiple changes value linearly without altering mortality. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   (k_1+k_2)y_t=k_1y_t+k_2y_t
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
import Definitions.Def_actuarial_e_salaryMultiple

open ActuarialDeathE

theorem actuarial_e_salary_multiple_linear (salary : ℕ → ℝ) (t : ℕ) (k1 k2 : ℝ) : salaryMultiple (k1 + k2) salary t = salaryMultiple k1 salary t + salaryMultiple k2 salary t := by sorry
