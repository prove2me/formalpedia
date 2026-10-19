-- Prove2me | Theorems.Thm_actuarial_e_overlap_zero_death_before_retirement
-- name    : actuarial_e_overlap_zero_death_before_retirement
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T18:27:55.122294+00:00
-- url     : https://prove2.me/theorems/5d560fbb-c67d-4762-a52b-f0e0f9d4e219
-- title:
--   No guarantee replacement for active or deferred death
-- statement:
--   No guarantee replacement for active or deferred death. Retirement guarantee terms do not affect pensions arising before commencement. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   i<r\quad\Rightarrow\quad O_t(i,j)=0
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

open ActuarialDeathE

theorem actuarial_e_overlap_zero_death_before_retirement (h r g i j t : ℕ) (c increase : ℕ → ℝ) (hi : i < r) : overlapPayment h r g i j t c increase = 0 := by sorry
