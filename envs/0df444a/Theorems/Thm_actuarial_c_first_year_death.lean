-- Prove2me | Theorems.Thm_actuarial_c_first_year_death
-- name    : actuarial_c_first_year_death
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T21:23:35.912548+00:00
-- url     : https://prove2.me/theorems/9d8d6a94-edc6-4a67-93ee-415e3ff1dd4d
-- title:
--   Certain first-year death pays at time one
-- statement:
--   Certain first-year death pays at time one.
--
--   Mathematical relation:
--
--   $$
--   p_0=1,\ p_j=0\ (j>0)\Longrightarrow A(b)=vb_0
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

theorem actuarial_c_first_year_death (h : ℕ) (v : ℝ) (b p : ℕ → ℝ) (hh : 0 < h) (hp : p 0 = 1) (hz : ∀ j, 0 < j → p j = 0) : epv h v b p=v*b 0 := by sorry
