-- Prove2me | Theorems.Thm_actuarial_e_retired_event_lump
-- name    : actuarial_e_retired_event_lump
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T22:39:59.124137+00:00
-- url     : https://prove2.me/theorems/49db2970-c4aa-4a73-9403-d19090091f49
-- title:
--   Retired death-event lump valuation
-- statement:
--   Retired death-event lump valuation. Post-commencement death triggers the retirement death-rider schedule. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   r\leq i<h,\ e\leq r\quad\Rightarrow\quad L(i)=L_R(i+1)
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
import Definitions.Def_actuarial_e_regimeLump

open ActuarialDeathE

theorem actuarial_e_retired_event_lump (h e r i : ℕ) (service defer retire : ℕ → ℝ) (he : e ≤ r) (hi : i < h) (hr : r ≤ i) : regimeLump h e r i service defer retire = retire (i + 1) := by sorry
