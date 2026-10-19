-- Prove2me | Theorems.Thm_actuarial_e_expect_scale
-- name    : actuarial_e_expect_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T21:52:28.769323+00:00
-- url     : https://prove2.me/theorems/5a0ead1f-ac27-4d0b-9ac1-cacf86da7d40
-- title:
--   Scale of a jointly contingent benefit
-- statement:
--   Scale of a jointly contingent benefit. Valuation is homogeneous in contractual cash amounts for a fixed joint mortality law. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   \mathbb{E}_p[kF]=k\mathbb{E}_p[F]
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

theorem actuarial_e_expect_scale (h : ℕ) (p f : ℕ → ℕ → ℝ) (k : ℝ) : expect h p (fun i j => k * f i j) = k * expect h p f := by sorry
