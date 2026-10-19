-- Prove2me | Theorems.Thm_actuarial_e_child_due_when_qualifying
-- name    : actuarial_e_child_due_when_qualifying
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T20:33:20.543462+00:00
-- url     : https://prove2.me/theorems/91dbbc3e-3344-4194-b40d-da2567327a9d
-- title:
--   Child payment requires member death, own survival and minimum age
-- statement:
--   Child payment requires member death, own survival and minimum age. A qualified dependant alive on the date receives one contractual instalment while below the cessation age. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   i+1<t\leq j,\ a_0+t<a_{\max}\ \Rightarrow\ C_{\text{child}}=1
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
import Definitions.Def_actuarial_e_childDue

open ActuarialDeathE

theorem actuarial_e_child_due_when_qualifying (i j t childAge maximumAge : ℕ) (hi : i + 1 < t) (hj : t ≤ j) (ha : childAge + t < maximumAge) : childDue i j t childAge maximumAge = 1 := by sorry
