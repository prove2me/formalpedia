-- Prove2me | Theorems.Thm_actuarial_e_retired_from_retirement
-- name    : actuarial_e_retired_from_retirement
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T17:45:24.691778+00:00
-- url     : https://prove2.me/theorems/3c861d71-0a40-42eb-9157-f7b83bc68c49
-- title:
--   Post-commencement death
-- statement:
--   Post-commencement death. Retirement benefits first become eligible in the year following the commencement anniversary. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   r\leq i<h\quad\Rightarrow\quad I_R(i)=1
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

theorem actuarial_e_retired_from_retirement (h r i : ℕ) (hi : i < h) (hr : r ≤ i) : retired h r i = 1 := by sorry
