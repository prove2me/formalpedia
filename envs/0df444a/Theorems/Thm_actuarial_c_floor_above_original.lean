-- Prove2me | Theorems.Thm_actuarial_c_floor_above_original
-- name    : actuarial_c_floor_above_original
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:22:29.850413+00:00
-- url     : https://prove2.me/theorems/f95a98ae-24fb-4cee-8532-4ee97f1747c9
-- title:
--   Floor preserves at least underlying death benefit
-- statement:
--   Floor preserves at least underlying death benefit.
--
--   Mathematical relation:
--
--   $$
--   \max(f,b_j)\ge b_j
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.2, variable death-benefit vector, printed p. 62. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_floorBenefit

open ActuarialAssurances

theorem actuarial_c_floor_above_original (f : ℝ) (b : ℕ → ℝ) (j : ℕ) : b j ≤ floorBenefit f b j := by sorry
