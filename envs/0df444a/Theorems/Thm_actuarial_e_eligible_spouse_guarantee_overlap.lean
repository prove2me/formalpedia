-- Prove2me | Theorems.Thm_actuarial_e_eligible_spouse_guarantee_overlap
-- name    : actuarial_e_eligible_spouse_guarantee_overlap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T18:26:56.406988+00:00
-- url     : https://prove2.me/theorems/fb684470-777a-49e0-aa60-6320945fcbbb
-- title:
--   Positive retiree-survivor overlap inside guarantee
-- statement:
--   Positive retiree-survivor overlap inside guarantee. The retiree's qualifying survivor instalment is excluded only in the replacement version. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   r\leq i<h,\ i+1<t\leq j,\ t<r+g\Rightarrow O_t(i,j)=u_tc_{i+1}
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

theorem actuarial_e_eligible_spouse_guarantee_overlap (h r g i j t : ℕ) (c increase : ℕ → ℝ) (hr : r ≤ i) (hi : i < h) (ht : i + 1 < t) (hj : t ≤ j) (hg : t < r + g) : overlapPayment h r g i j t c increase = c (i + 1) * increase t := by sorry
