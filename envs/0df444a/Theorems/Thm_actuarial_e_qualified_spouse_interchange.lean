-- Prove2me | Theorems.Thm_actuarial_e_qualified_spouse_interchange
-- name    : actuarial_e_qualified_spouse_interchange
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T20:01:28.004152+00:00
-- url     : https://prove2.me/theorems/8b20f912-17dc-4e68-a601-51c3dbe64b94
-- title:
--   Freeze spouse qualification at death before valuing instalments
-- statement:
--   Freeze spouse qualification at death before valuing instalments. Event-first integration with a single qualifying-spouse probability is identical to date-first survivor cashflow valuation. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   V_R(q,\eta)=\mathbb{E}_p\left[q_i\sum_t v_tR_t(i,j;\eta)\right]
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
import Definitions.Def_actuarial_e_expect
import Definitions.Def_actuarial_e_spousePayment
import Definitions.Def_actuarial_e_qualifiedSpouseEPV

open ActuarialDeathE

theorem actuarial_e_qualified_spouse_interchange (h n e r g : ℕ) (p : ℕ → ℕ → ℝ) (q disc a b c increase : ℕ → ℝ) (replace : Bool) : qualifiedSpouseEPV h n e r g p q disc a b c increase replace = expect h p (fun i j => q i * ∑ t ∈ Finset.range n, disc t * spousePayment h e r g i j t a b c increase replace) := by sorry
