-- Prove2me | Theorems.Thm_actuarial_c_inc_dec_level
-- name    : actuarial_c_inc_dec_level
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:22:05.088361+00:00
-- url     : https://prove2.me/theorems/f9e71ba4-5cce-4808-8e41-998d32717ad8
-- title:
--   Increasing and decreasing schedules sum to a level insured amount
-- statement:
--   Increasing and decreasing schedules sum to a level insured amount.
--
--   Mathematical relation:
--
--   $$
--   b^{\uparrow}_j+b^{\downarrow}_j=n+1,\quad j<n
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.2, variable death-benefit vector, printed p. 62. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_inc
import Definitions.Def_actuarial_c_dec

open ActuarialAssurances

theorem actuarial_c_inc_dec_level (n j : ℕ) (hj : j < n) : inc j+dec n j=(n+1 : ℕ) := by sorry
