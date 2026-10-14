-- Prove2me | Theorems.Thm_actuarial_c_second_scale
-- name    : actuarial_c_second_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:24:06.707713+00:00
-- url     : https://prove2.me/theorems/9b407b22-738d-4f2d-9152-e00e289d3438
-- title:
--   Claim second moment varies with squared sum assured
-- statement:
--   Claim second moment varies with squared sum assured.
--
--   Mathematical relation:
--
--   $$
--   \mathbb{E}[(cZ)^2]=c^2\mathbb{E}[Z^2]
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

theorem actuarial_c_second_scale (h : ℕ) (v c : ℝ) (b p : ℕ → ℝ) : second h v (fun j => c*b j) p=c^2*second h v b p := by sorry
