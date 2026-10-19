-- Prove2me | Theorems.Thm_actuarial_e_child_EPVs_nonneg
-- name    : actuarial_e_child_EPVs_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T20:42:09.157892+00:00
-- url     : https://prove2.me/theorems/c0c346cb-065d-46c6-b0e3-f73b80645dc1
-- title:
--   Nonnegative age-limited dependent pension under valid survival assumptions
-- statement:
--   Nonnegative age-limited dependent pension under valid survival assumptions. With nonnegative actual payments, discount factors, and joint probabilities, the child's expected pension value is nonnegative. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   p,v,b,u\geq0\ \Rightarrow\ V_{\text{child,event}}\geq0
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
import Definitions.Def_actuarial_e_validLaw
import Definitions.Def_actuarial_e_childEventEPV

open ActuarialDeathE

theorem actuarial_e_child_EPVs_nonneg (h n childAge maximumAge : ℕ) (p : ℕ → ℕ → ℝ) (disc basis increase : ℕ → ℝ) (hp : validLaw h p) (hd : ∀ t ∈ Finset.range n, 0 ≤ disc t) (hb : ∀ i ∈ Finset.range (h + 1), 0 ≤ basis (i + 1)) (hu : ∀ t ∈ Finset.range n, 0 ≤ increase t) : 0 ≤ childEventEPV h n childAge maximumAge p disc basis increase := by sorry
