-- Prove2me | Theorems.Thm_actuarial_c_no_interest_claim
-- name    : actuarial_c_no_interest_claim
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T21:25:15.482881+00:00
-- url     : https://prove2.me/theorems/3d0c76be-8fd3-484c-8e28-8fbf77975aa1
-- title:
--   Zero interest reduces EPV to death-event weighted sums
-- statement:
--   Zero interest reduces EPV to death-event weighted sums.
--
--   Mathematical relation:
--
--   $$
--   \mathbb{E}[Z]\big|_{v=1}=\sum_{j=0}^{h-1}b_jp_j
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

theorem actuarial_c_no_interest_claim (h : ℕ) (b p : ℕ → ℝ) : epv h 1 b p=∑ j ∈ Finset.range h, b j*p j := by sorry
