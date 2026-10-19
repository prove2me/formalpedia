-- Prove2me | Theorems.Thm_actuarial_c_benefit_order
-- name    : actuarial_c_benefit_order
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:22:59.209977+00:00
-- url     : https://prove2.me/theorems/1149b392-72c4-443f-b9d4-58790bae85b4
-- title:
--   Nonnegative mortality and discount preserve benefit ordering
-- statement:
--   Nonnegative mortality and discount preserve benefit ordering.
--
--   Mathematical relation:
--
--   $$
--   b_j\le c_j\Longrightarrow A(b)\le A(c)
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

open ActuarialAssurances

theorem actuarial_c_benefit_order (h : ℕ) (v : ℝ) (b c p : ℕ → ℝ) (hv : 0 ≤ v) (hp : ∀ j, 0 ≤ p j) (hbc : ∀ j, b j ≤ c j) : epv h v b p ≤ epv h v c p := by sorry
