-- Prove2me | Theorems.Thm_actuarial_c_moment_zero
-- name    : actuarial_c_moment_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:25:04.821992+00:00
-- url     : https://prove2.me/theorems/07a336f4-2692-40c7-9127-f125319b7f76
-- title:
--   No benefit gives zero second claim moment
-- statement:
--   No benefit gives zero second claim moment.
--
--   Mathematical relation:
--
--   $$
--   \mathbb{E}[Z_0^2]=0
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.2, benefit random present value as context, printed p. 62. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_second

open ActuarialAssurances

theorem actuarial_c_moment_zero (h : ℕ) (v : ℝ) (p : ℕ → ℝ) : second h v (fun _ => 0) p=0 := by sorry
