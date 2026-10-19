-- Prove2me | Theorems.Thm_actuarial_e_guarantee_capital_nonneg
-- name    : actuarial_e_guarantee_capital_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T20:57:13.155721+00:00
-- url     : https://prove2.me/theorems/7981bc1e-15ce-42a7-8cdf-20c8d739ddda
-- title:
--   Nonnegative guaranteed cash and forward factors yield nonnegative commutation
-- statement:
--   Nonnegative guaranteed cash and forward factors yield nonnegative commutation. Provided the contracted guaranteed pension and all forward factors are nonnegative, the estate's capital amount cannot be negative. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   G_t\geq0,\ f_{i+1,t}\geq0\Rightarrow K_{i+1}\geq0
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
import Definitions.Def_actuarial_e_guaranteeCapitalAtDeath

open ActuarialDeathE

theorem actuarial_e_guarantee_capital_nonneg (n h r g i : ℕ) (forward : ℕ → ℕ → ℝ) (base : ℕ → ℝ) (hf : ∀ t ∈ Finset.range n, 0 ≤ forward (i + 1) t) (hb : ∀ t ∈ Finset.range n, 0 ≤ base t) : 0 ≤ guaranteeCapitalAtDeath n h r g i forward base := by sorry
