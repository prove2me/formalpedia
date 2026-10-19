-- Prove2me | Theorems.Thm_actuarial_e_qualified_spouse_all
-- name    : actuarial_e_qualified_spouse_all
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T19:56:46.596955+00:00
-- url     : https://prove2.me/theorems/7656c9ff-a9cb-48ef-9d72-5221ca4207d1
-- title:
--   Certain qualifying spouse recovers the fixed-spouse valuation
-- statement:
--   Certain qualifying spouse recovers the fixed-spouse valuation. When qualification at death is certain, the survivor pension uses only the actual dependent life and payment-date survival. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   q_i=1\ \Rightarrow\ V_R(q,\eta)=V_R(1,\eta)
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
import Definitions.Def_actuarial_e_spouseEPV
import Definitions.Def_actuarial_e_qualifiedSpouseEPV

open ActuarialDeathE

theorem actuarial_e_qualified_spouse_all (h n e r g : ℕ) (p : ℕ → ℕ → ℝ) (disc a b c increase : ℕ → ℝ) (replace : Bool) : qualifiedSpouseEPV h n e r g p (fun i => (1 : ℝ)) disc a b c increase replace = spouseEPV h n e r g p disc a b c increase replace := by sorry
