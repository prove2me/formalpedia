-- Prove2me | Theorems.Thm_actuarial_e_deferred_event_lump
-- name    : actuarial_e_deferred_event_lump
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T22:23:50.251453+00:00
-- url     : https://prove2.me/theorems/5cb2505e-77e7-49ef-8f0d-7cfbe3ec0e2e
-- title:
--   Deferred death-event lump valuation
-- statement:
--   Deferred death-event lump valuation. Exit precedes death, pension commencement follows, and the preserved-right schedule applies. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   e\leq i<r,\ i<h\quad\Rightarrow\quad L(i)=L_D(i+1)
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

theorem actuarial_e_deferred_event_lump (h e r i : ℕ) (service defer retire : ℕ → ℝ) (he : e ≤ r) (hi : i < h) (h1 : e ≤ i) (h2 : i < r) : regimeLump h e r i service defer retire = defer (i + 1) := by sorry
