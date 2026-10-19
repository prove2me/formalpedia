-- Prove2me | Theorems.Thm_actuarial_e_no_guarantee_no_overlap
-- name    : actuarial_e_no_guarantee_no_overlap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T09:02:16.614723+00:00
-- url     : https://prove2.me/theorems/b41e3e5e-668c-4aad-b4a5-189aa3ef1c10
-- title:
--   Zero guarantee has no survivor offset
-- statement:
--   Zero guarantee has no survivor offset. When no guarantee is granted the gross and replacement contracts have equal expected value. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   g=0\quad\Rightarrow\quad V_O=0
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
import Definitions.Def_actuarial_e_overlapEPV

open ActuarialDeathE

theorem actuarial_e_no_guarantee_no_overlap (h n r : ℕ) (p : ℕ → ℕ → ℝ) (disc basis increase : ℕ → ℝ) : overlapEPV h n r 0 p disc basis increase = 0 := by sorry
