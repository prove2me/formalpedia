-- Prove2me | Theorems.Thm_actuarial_e_spouse_same_after_guarantee
-- name    : actuarial_e_spouse_same_after_guarantee
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-17T05:31:37.285574+00:00
-- url     : https://prove2.me/theorems/a52a5c24-c4ec-47ea-a95b-c4e688ccc49f
-- title:
--   Survivor pension restored at expiry
-- statement:
--   Survivor pension restored at expiry. The survivor pension switches are equivalent after the guarantee term ends. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   r+g\leq t\quad\Rightarrow\quad R_t(i,j;0)=R_t(i,j;1)
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
import Definitions.Def_actuarial_e_spousePayment

open ActuarialDeathE

theorem actuarial_e_spouse_same_after_guarantee (h e r g i j t : ℕ) (a b c increase : ℕ → ℝ) (ht : r + g ≤ t) : spousePayment h e r g i j t a b c increase false = spousePayment h e r g i j t a b c increase true := by sorry
