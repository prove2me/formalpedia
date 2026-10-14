-- Prove2me | Theorems.Thm_actuarial_c_premium_due_nonneg
-- name    : actuarial_c_premium_due_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:25:43.794751+00:00
-- url     : https://prove2.me/theorems/84c9a690-c063-4b8e-82f4-491ff1166201
-- title:
--   A nonnegative premium annuity denominator
-- statement:
--   A nonnegative premium annuity denominator.
--
--   Mathematical relation:
--
--   $$
--   \ddot a_n=\sum_{j=0}^{n-1}v^jS(j)\ge0
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.2, net premium ratio and premium stream, printed p. 63. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_surv
import Definitions.Def_actuarial_c_due

open ActuarialAssurances

theorem actuarial_c_premium_due_nonneg (h n : ℕ) (v : ℝ) (p : ℕ → ℝ) (hv : 0 ≤ v) (hp : ∀ j, 0 ≤ p j) : 0 ≤ due h n v p := by sorry
