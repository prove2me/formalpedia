-- Prove2me | Theorems.Thm_actuarial_e_retired_before_retirement
-- name    : actuarial_e_retired_before_retirement
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T17:45:15.131704+00:00
-- url     : https://prove2.me/theorems/383fa318-54e7-4875-85be-c113e64225b4
-- title:
--   Retirement death benefit requires commencement
-- statement:
--   Retirement death benefit requires commencement. The death regime excludes members who die before their pension has commenced. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   i<r\quad\Rightarrow\quad I_R(i)=0
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
import Definitions.Def_actuarial_e_retired

open ActuarialDeathE

theorem actuarial_e_retired_before_retirement (h r i : ℕ) (hi : i < r) : retired h r i = 0 := by sorry
