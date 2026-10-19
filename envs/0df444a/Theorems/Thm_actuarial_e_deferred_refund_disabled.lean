-- Prove2me | Theorems.Thm_actuarial_e_deferred_refund_disabled
-- name    : actuarial_e_deferred_refund_disabled
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T22:22:45.662419+00:00
-- url     : https://prove2.me/theorems/64b128d7-d395-401b-936c-c5cf8f15b3ec
-- title:
--   Deferred rights without refund
-- statement:
--   Deferred rights without refund. The revalued preserved benefit is retained when contributions are not separately refundable. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   L_D(t;0)=P_{\text{exit}}G_t\mathcal{A}_t
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
import Definitions.Def_actuarial_e_revaluedDeferred
import Definitions.Def_actuarial_e_deferredBundle

open ActuarialDeathE

theorem actuarial_e_deferred_refund_disabled (atExit : ℝ) (growth capitalFactor refund : ℕ → ℝ) (t : ℕ) : deferredBundle atExit growth capitalFactor refund false t = revaluedDeferred atExit growth t * capitalFactor t := by sorry
