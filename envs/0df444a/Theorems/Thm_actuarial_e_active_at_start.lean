-- Prove2me | Theorems.Thm_actuarial_e_active_at_start
-- name    : actuarial_e_active_at_start
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T17:43:53.045495+00:00
-- url     : https://prove2.me/theorems/4a975637-feee-46a4-aef4-05e283ae1370
-- title:
--   Death in the first employment year
-- statement:
--   Death in the first employment year. A death in (0,1] is an active-service event when employment and censoring both extend beyond time zero. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   0<h,\ 0<e\quad\Rightarrow\quad I_A(0)=1
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

open ActuarialDeathE

theorem actuarial_e_active_at_start (h e : ℕ) (he : 0 < h) (he2 : 0 < e) : active h e 0 = 1 := by sorry
