-- Prove2me | Theorems.Thm_actuarial_c_floor_epv_order
-- name    : actuarial_c_floor_epv_order
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T21:23:11.262204+00:00
-- url     : https://prove2.me/theorems/d39f07c2-5f8c-4285-9d9f-ed70d50e9150
-- title:
--   Floored death benefit cannot reduce expected claim
-- statement:
--   Floored death benefit cannot reduce expected claim.
--
--   Mathematical relation:
--
--   $$
--   A(b)\le A(\max(f,b))
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.2, variable death-benefit vector, printed p. 62. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_epv
import Definitions.Def_actuarial_c_floorBenefit

open ActuarialAssurances

theorem actuarial_c_floor_epv_order (h : ℕ) (v f : ℝ) (b p : ℕ → ℝ) (hv : 0 ≤ v) (hp : ∀ j, 0 ≤ p j) : epv h v b p ≤ epv h v (floorBenefit f b) p := by sorry
