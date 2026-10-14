-- Prove2me | Theorems.Thm_actuarial_c_variance_nonneg
-- name    : actuarial_c_variance_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T21:24:43.50908+00:00
-- url     : https://prove2.me/theorems/2510ed2e-2f51-4104-b186-af2e80c7e30f
-- title:
--   Normalised nonnegative mortality gives nonnegative variance
-- statement:
--   Normalised nonnegative mortality gives nonnegative variance.
--
--   Mathematical relation:
--
--   $$
--   \operatorname{Var}(Z)\ge0
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.2, benefit random present value as context, printed p. 62. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_total
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_epv
import Definitions.Def_actuarial_c_second
import Definitions.Def_actuarial_c_variance

open ActuarialAssurances

theorem actuarial_c_variance_nonneg (h : ℕ) (v : ℝ) (b p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (hm : total h p=1) : 0 ≤ variance h v b p := by sorry
