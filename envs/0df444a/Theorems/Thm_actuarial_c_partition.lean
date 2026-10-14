-- Prove2me | Theorems.Thm_actuarial_c_partition
-- name    : actuarial_c_partition
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T21:15:10.03627+00:00
-- url     : https://prove2.me/theorems/f8790d37-a325-4ac3-99d9-a00bb2dfe6f0
-- title:
--   Deaths before maturity and survivors partition states
-- statement:
--   Deaths before maturity and survivors partition states.
--
--   Mathematical relation:
--
--   $$
--   \sum_{j=0}^{n-1}p_j+S(n)=1
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Sections 5.1–5.2, occurrence and death-year timing, printed p. 61. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_total
import Definitions.Def_actuarial_c_surv

open ActuarialAssurances

theorem actuarial_c_partition (h n : ℕ) (p : ℕ → ℝ) (hn : n ≤ h) : (∑ j ∈ Finset.range n, p j)+surv h p n=total h p := by sorry
