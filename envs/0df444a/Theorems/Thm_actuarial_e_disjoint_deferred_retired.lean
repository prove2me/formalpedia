-- Prove2me | Theorems.Thm_actuarial_e_disjoint_deferred_retired
-- name    : actuarial_e_disjoint_deferred_retired
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T17:48:27.532082+00:00
-- url     : https://prove2.me/theorems/928f22c7-c021-480d-975a-4b2c9f602ea9
-- title:
--   Disjoint deferred and retired deaths
-- statement:
--   Disjoint deferred and retired deaths. A single member death cannot trigger both of these regime-specific lump sums. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   I_D(i)I_R(i)=0
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
import Definitions.Def_actuarial_e_deferred
import Definitions.Def_actuarial_e_retired

open ActuarialDeathE

theorem actuarial_e_disjoint_deferred_retired (h e r i : ℕ) (her : e ≤ r) : deferred h e r i * retired h r i = 0 := by sorry
