-- Prove2me | Theorems.Thm_actuarial_e_child_EPVs_equivalent
-- name    : actuarial_e_child_EPVs_equivalent
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T20:37:03.357606+00:00
-- url     : https://prove2.me/theorems/b2363d44-770d-4d24-b0d5-f338b5a65c0a
-- title:
--   Event-first equals payment-first EPV for an age-limited child
-- statement:
--   Event-first equals payment-first EPV for an age-limited child. The same mortality event, child-age restriction, discount factor and survivor payment basis reconcile under finite sum interchange. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   V_{\text{child,event}}=V_{\text{child,date}}
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
import Definitions.Def_actuarial_e_childEventEPV
import Definitions.Def_actuarial_e_childDatedEPV

open ActuarialDeathE

theorem actuarial_e_child_EPVs_equivalent (h n childAge maximumAge : ℕ) (p : ℕ → ℕ → ℝ) (disc basis increase : ℕ → ℝ) : childEventEPV h n childAge maximumAge p disc basis increase = childDatedEPV h n childAge maximumAge p disc basis increase := by sorry
