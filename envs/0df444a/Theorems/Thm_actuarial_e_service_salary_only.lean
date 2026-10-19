-- Prove2me | Theorems.Thm_actuarial_e_service_salary_only
-- name    : actuarial_e_service_salary_only
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T21:54:14.938047+00:00
-- url     : https://prove2.me/theorems/5a96691c-d126-4860-8367-c039cc1708c9
-- title:
--   Scheme-selected service benefit
-- statement:
--   Scheme-selected service benefit. Only the salary multiple is promised; the other features are contractually switched off. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   L_A(t;1,0,0)=ky_t
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
import Definitions.Def_actuarial_e_serviceBundle

open ActuarialDeathE

theorem actuarial_e_service_salary_only (k : ℝ) (salary accrued contributions : ℕ → ℝ) (t : ℕ) : serviceBundle k salary accrued contributions true false false t = salaryMultiple k salary t := by sorry
