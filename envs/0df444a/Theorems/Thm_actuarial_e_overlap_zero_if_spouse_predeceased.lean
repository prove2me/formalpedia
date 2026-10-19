-- Prove2me | Theorems.Thm_actuarial_e_overlap_zero_if_spouse_predeceased
-- name    : actuarial_e_overlap_zero_if_spouse_predeceased
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T18:27:45.025223+00:00
-- url     : https://prove2.me/theorems/4e9fe196-ba44-40e8-929f-697da107fbc4
-- title:
--   No replacement effect for a predeceased dependent
-- statement:
--   No replacement effect for a predeceased dependent. The guarantee may remain an estate promise, whereas the spouse stream is never established. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   j\leq i\quad\Rightarrow\quad O_t(i,j)=0
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
import Definitions.Def_actuarial_e_overlapPayment

open ActuarialDeathE

theorem actuarial_e_overlap_zero_if_spouse_predeceased (h r g i j t : ℕ) (c increase : ℕ → ℝ) (hj : j ≤ i) : overlapPayment h r g i j t c increase = 0 := by sorry
