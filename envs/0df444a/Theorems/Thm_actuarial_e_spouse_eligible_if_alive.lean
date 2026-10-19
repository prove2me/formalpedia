-- Prove2me | Theorems.Thm_actuarial_e_spouse_eligible_if_alive
-- name    : actuarial_e_spouse_eligible_if_alive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T21:34:07.082712+00:00
-- url     : https://prove2.me/theorems/b3bd1562-f1f5-4518-9a3b-77c1ba8fc6bd
-- title:
--   Spouse alive on member-death anniversary
-- statement:
--   Spouse alive on member-death anniversary. Marriage or dependent eligibility is assessed once, before subsequent survivor instalments. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   i<j\quad\Rightarrow\quad Q(i,j)=1
--   $$
--
--   This is an open theorem statement; no formal proof is claimed. Amounts are per instalment or in pounds as appropriate; probabilities are dimensionless and discounts are to valuation.
-- source:
--   Originally derived finite-grid pension contract statement, based on the actuarial context in Chapter 9, p. 359, of Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, 3rd ed, Chapters 8–11. https://doi.org/10.1017/9781108784184 Specific benefit switches and endpoint rules are explicit new scheme assumptions, not verbatim textbook results.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_spouseEligible

open ActuarialDeathE

theorem actuarial_e_spouse_eligible_if_alive (i j : ℕ) (h : i < j) : spouseEligible i j = 1 := by sorry
