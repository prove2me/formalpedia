-- Prove2me | Theorems.Thm_actuarial_e_expect_add
-- name    : actuarial_e_expect_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T21:43:27.521702+00:00
-- url     : https://prove2.me/theorems/d8878ac3-1f15-4d5b-8b09-8b23e8863d4b
-- title:
--   Expected value of disjoint and overlapping benefits
-- statement:
--   Expected value of disjoint and overlapping benefits. Linearity permits independent cashflow streams to be priced without independent lifetimes. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   \mathbb{E}_p[F+H]=\mathbb{E}_p[F]+\mathbb{E}_p[H]
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
import Definitions.Def_actuarial_e_expect

open ActuarialDeathE

theorem actuarial_e_expect_add (h : ℕ) (p f g : ℕ → ℕ → ℝ) : expect h p (fun i j => f i j + g i j) = expect h p f + expect h p g := by sorry
