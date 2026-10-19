-- Prove2me | Theorems.Thm_actuarial_e_qualified_spouse_overlap
-- name    : actuarial_e_qualified_spouse_overlap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T20:02:30.637485+00:00
-- url     : https://prove2.me/theorems/0cbc102f-8e40-43f5-942e-cbc88075ebdb
-- title:
--   Qualifying-dependent probability preserves exact guarantee coordination
-- statement:
--   Qualifying-dependent probability preserves exact guarantee coordination. The replacement correction remains the independently priced mortality-conditional spouse stream rather than a residual value. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   V_R(q,0)=V_R(q,1)+V_O(q)
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
import Definitions.Def_actuarial_e_qualifiedSpouseEPV
import Definitions.Def_actuarial_e_qualifiedOverlapEPV

open ActuarialDeathE

theorem actuarial_e_qualified_spouse_overlap (h n e r g : ℕ) (p : ℕ → ℕ → ℝ) (q disc a b c increase : ℕ → ℝ) : qualifiedSpouseEPV h n e r g p q disc a b c increase false = qualifiedSpouseEPV h n e r g p q disc a b c increase true + qualifiedOverlapEPV h n r g p q disc c increase := by sorry
