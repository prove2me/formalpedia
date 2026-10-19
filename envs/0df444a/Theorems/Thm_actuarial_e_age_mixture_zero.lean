-- Prove2me | Theorems.Thm_actuarial_e_age_mixture_zero
-- name    : actuarial_e_age_mixture_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T20:04:53.807287+00:00
-- url     : https://prove2.me/theorems/8734b68f-bcbb-474f-ae8f-b289bc3c018b
-- title:
--   No spouse-age scenario means no joint mass
-- statement:
--   No spouse-age scenario means no joint mass. A completely empty age-difference distribution contains no qualifying mortality scenario. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   a=0\ \Rightarrow\ p_{ij}^{\text{mix}}=0
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
import Definitions.Def_actuarial_e_ageMixtureLaw

open ActuarialDeathE

theorem actuarial_e_age_mixture_zero (h : ℕ) (w : ℕ → ℝ) (laws : ℕ → ℕ → ℕ → ℝ) (i j : ℕ) : ageMixtureLaw h 0 w laws i j = 0 := by sorry
