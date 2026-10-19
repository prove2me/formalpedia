-- Prove2me | Theorems.Thm_actuarial_e_qualified_overlap_interchange
-- name    : actuarial_e_qualified_overlap_interchange
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T20:01:46.140531+00:00
-- url     : https://prove2.me/theorems/52d513e0-0829-4f66-ae3b-e5d94c1c0a5f
-- title:
--   Death-fixed marriage probability in guarantee overlap
-- statement:
--   Death-fixed marriage probability in guarantee overlap. Only the properly eligible surviving spouse's payments are suppressed, weighted once at member death. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   V_O(q)=\mathbb{E}_p\left[q_i\sum_t v_tO_t(i,j)\right]
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
import Definitions.Def_actuarial_e_overlapPayment
import Definitions.Def_actuarial_e_qualifiedOverlapEPV

open ActuarialDeathE

theorem actuarial_e_qualified_overlap_interchange (h n r g : ℕ) (p : ℕ → ℕ → ℝ) (q disc c increase : ℕ → ℝ) : qualifiedOverlapEPV h n r g p q disc c increase = expect h p (fun i j => q i * ∑ t ∈ Finset.range n, disc t * overlapPayment h r g i j t c increase) := by sorry
