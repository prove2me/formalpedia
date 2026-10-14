-- Prove2me | Theorems.Thm_actuarial_c_delay_zero
-- name    : actuarial_c_delay_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:27:15.331702+00:00
-- url     : https://prove2.me/theorems/14bb1762-6d4c-4f4c-8f0b-ee646a8a136c
-- title:
--   With zero settlement delay the death claim has the original year-end valuation
-- statement:
--   With zero settlement delay the death claim has the original year-end valuation.
--
--   Mathematical relation:
--
--   $$
--   A^{\text{delay}}(0)=A
--   $$
--
--   The declared assumptions restrict the life law, discount and coverage exactly as required. This is an open actuarial theorem, derived from realised claim events or their expected values.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.1, claim processing and payment timing, printed p. 61. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_epv
import Definitions.Def_actuarial_c_delayPath
import Definitions.Def_actuarial_c_delayEPV

open ActuarialAssurances

theorem actuarial_c_delay_zero (h : ℕ) (v : ℝ) (b p : ℕ → ℝ) : delayEPV h 0 v b p=epv h v b p := by sorry
