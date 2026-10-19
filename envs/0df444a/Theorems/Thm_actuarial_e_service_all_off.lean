-- Prove2me | Theorems.Thm_actuarial_e_service_all_off
-- name    : actuarial_e_service_all_off
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T22:22:10.421897+00:00
-- url     : https://prove2.me/theorems/1deb8327-93f0-48e5-a38f-c03378893bb0
-- title:
--   Scheme-selected service benefit
-- statement:
--   Scheme-selected service benefit. No active death lump component is payable; the other features are contractually switched off. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   L_A(t;0,0,0)=0
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
import Definitions.Def_actuarial_e_serviceBundle

open ActuarialDeathE

theorem actuarial_e_service_all_off (k : ℝ) (salary accrued contributions : ℕ → ℝ) (t : ℕ) : serviceBundle k salary accrued contributions false false false t = 0 := by sorry
