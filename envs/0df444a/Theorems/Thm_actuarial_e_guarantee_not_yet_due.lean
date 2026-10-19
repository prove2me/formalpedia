-- Prove2me | Theorems.Thm_actuarial_e_guarantee_not_yet_due
-- name    : actuarial_e_guarantee_not_yet_due
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-17T04:57:29.541979+00:00
-- url     : https://prove2.me/theorems/1410fab3-0640-4b74-b108-2aefc2733433
-- title:
--   No estate continuation during member's lifetime
-- statement:
--   No estate continuation during member's lifetime. The guarantee replaces the ceased member instalment only after death. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   t\leq i\quad\Rightarrow\quad G_t(i)=0
--   $$
--
--   This is an open theorem statement; no formal proof is claimed. Amounts are per instalment or in pounds as appropriate; probabilities are dimensionless and discounts are to valuation.
-- source:
--   Originally derived finite-grid pension contract statement, based on the actuarial context in Chapter 10, p. 388, of Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, 3rd ed, Chapters 8–11. https://doi.org/10.1017/9781108784184 Specific benefit switches and endpoint rules are explicit new scheme assumptions, not verbatim textbook results.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_guaranteePayment

open ActuarialDeathE

theorem actuarial_e_guarantee_not_yet_due (h r g i t : ℕ) (base : ℕ → ℝ) (ht : t ≤ i) : guaranteePayment h r g i t base = 0 := by sorry
