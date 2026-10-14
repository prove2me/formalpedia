-- Prove2me | Theorems.Thm_actuarial_c_decrease_last
-- name    : actuarial_c_decrease_last
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:21:51.317983+00:00
-- url     : https://prove2.me/theorems/0ac6abaa-af79-4ec4-984b-fb6fc0e44a18
-- title:
--   Decreasing term final covered year equals one unit
-- statement:
--   Decreasing term final covered year equals one unit.
--
--   Mathematical relation:
--
--   $$
--   b^{\downarrow}_{n-1}=1
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.2, variable death-benefit vector, printed p. 62. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_dec

open ActuarialAssurances

theorem actuarial_c_decrease_last (n : ℕ) (hn : 0 < n) : dec n (n-1)=1 := by sorry
