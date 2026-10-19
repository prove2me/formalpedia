-- Prove2me | Theorems.Thm_actuarial_e_zero_cashflow_horizon
-- name    : actuarial_e_zero_cashflow_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T08:33:29.669682+00:00
-- url     : https://prove2.me/theorems/6081d9cf-e98f-49e6-a495-8ec221418f33
-- title:
--   Empty payment horizon
-- statement:
--   Empty payment horizon. The absence of scheduled pension payments leaves genuine death settlement liabilities intact. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   Z(i,j;\eta,n=0)=v_{i+1}L(i)
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
import Definitions.Def_actuarial_e_deathPV
import Definitions.Def_actuarial_e_realisedPV

open ActuarialDeathE

theorem actuarial_e_zero_cashflow_horizon (h e r g i j : ℕ) (disc service defer retire base a b c increase : ℕ → ℝ) (replace : Bool) : realisedPV h 0 e r g i j disc service defer retire base a b c increase replace = deathPV h e r i disc service defer retire := by sorry
