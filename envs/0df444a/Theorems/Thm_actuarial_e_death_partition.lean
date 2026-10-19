-- Prove2me | Theorems.Thm_actuarial_e_death_partition
-- name    : actuarial_e_death_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T17:45:36.690193+00:00
-- url     : https://prove2.me/theorems/92a43cf2-766d-4d5e-8fa9-1b83611a4c33
-- title:
--   Exhaustive mutually exclusive death regimes
-- statement:
--   Exhaustive mutually exclusive death regimes. Every uncensored death is active, deferred or retired when employment exit precedes retirement. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   i<h,\ e\leq r\quad\Rightarrow\quad I_A(i)+I_D(i)+I_R(i)=1
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

theorem actuarial_e_death_partition (h e r i : ℕ) (her : e ≤ r) (hi : i < h) : active h e i + deferred h e r i + retired h r i = 1 := by sorry
