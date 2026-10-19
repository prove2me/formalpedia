-- Prove2me | Theorems.Thm_actuarial_e_death_after_horizon
-- name    : actuarial_e_death_after_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T17:52:15.791041+00:00
-- url     : https://prove2.me/theorems/148433e8-e377-4f19-aa96-0b663edb943e
-- title:
--   Censoring removes event liabilities
-- statement:
--   Censoring removes event liabilities. The terminal member state represents no death within the priced horizon. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   I_A(h)+I_D(h)+I_R(h)=0
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
import Definitions.Def_actuarial_e_deferred
import Definitions.Def_actuarial_e_retired

open ActuarialDeathE

theorem actuarial_e_death_after_horizon (h e r : ℕ) : active h e h + deferred h e r h + retired h r h = 0 := by sorry
