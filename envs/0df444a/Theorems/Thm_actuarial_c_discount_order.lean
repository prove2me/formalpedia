-- Prove2me | Theorems.Thm_actuarial_c_discount_order
-- name    : actuarial_c_discount_order
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T21:25:28.306737+00:00
-- url     : https://prove2.me/theorems/c0c87e0e-0ccc-4d35-b756-77d6862b0f3b
-- title:
--   Larger discount factor increases nonnegative delayed death claims
-- statement:
--   Larger discount factor increases nonnegative delayed death claims.
--
--   Mathematical relation:
--
--   $$
--   0\le v\le w\Longrightarrow A_v(b)\le A_w(b)
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.2, benefit random present value as context, printed p. 62. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_epv

open ActuarialAssurances

theorem actuarial_c_discount_order (h : ℕ) (v w : ℝ) (b p : ℕ → ℝ) (hv : 0 ≤ v) (hvw : v ≤ w) (hp : ∀ j, 0 ≤ p j) (hb : ∀ j, 0 ≤ b j) : epv h v b p ≤ epv h w b p := by sorry
