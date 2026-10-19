-- Prove2me | Theorems.Thm_actuarial_e_age_mixture_active_mass
-- name    : actuarial_e_age_mixture_active_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T20:14:58.587987+00:00
-- url     : https://prove2.me/theorems/f84bd31a-0e3b-49a9-9b90-0be6d289272e
-- title:
--   Probability of death in service under age-difference mixing
-- statement:
--   Probability of death in service under age-difference mixing. Death-event probabilities under a common conditional career path are the weighted scenario-specific death-event probabilities. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   \Pr(A)_{\text{mix}}=\sum_kw_k\Pr(A\mid k)
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
import Definitions.Def_actuarial_e_activeDeathMass
import Definitions.Def_actuarial_e_ageMixtureLaw

open ActuarialDeathE

theorem actuarial_e_age_mixture_active_mass (h a e : ℕ) (w : ℕ → ℝ) (laws : ℕ → ℕ → ℕ → ℝ) : activeDeathMass h e (ageMixtureLaw h a w laws) = ∑ k ∈ Finset.range a, w k * activeDeathMass h e (laws k) := by sorry
