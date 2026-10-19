-- Prove2me | Theorems.Thm_actuarial_e_disjoint_active_retired
-- name    : actuarial_e_disjoint_active_retired
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T17:45:58.612979+00:00
-- url     : https://prove2.me/theorems/f8c62ab3-0eb8-49be-b030-25a385d51b7b
-- title:
--   Disjoint active and retired deaths
-- statement:
--   Disjoint active and retired deaths. A single member death cannot trigger both of these regime-specific lump sums. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   I_A(i)I_R(i)=0
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
import Definitions.Def_actuarial_e_active
import Definitions.Def_actuarial_e_retired

open ActuarialDeathE

theorem actuarial_e_disjoint_active_retired (h e r i : ℕ) (her : e ≤ r) : active h e i * retired h r i = 0 := by sorry
