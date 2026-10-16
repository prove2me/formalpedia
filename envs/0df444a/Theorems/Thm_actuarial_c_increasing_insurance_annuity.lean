-- Prove2me | Theorems.Thm_actuarial_c_increasing_insurance_annuity
-- name    : actuarial_c_increasing_insurance_annuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:29:37.914118+00:00
-- url     : https://prove2.me/theorems/56c1cb8a-c7e2-45bf-9323-fca02425f985
-- title:
--   Increasing death assurance relates to increasing temporary annuities with the censored-terminal correction
-- statement:
--   Increasing death assurance relates to increasing temporary annuities with the censored-terminal correction.
--
--   Mathematical relation:
--
--   $$
--   A(b^{\uparrow})+(1-v)I\ddot a_h+hv^hS(h)=\ddot a_h
--   $$
--
--   The declared assumptions restrict the life law, discount and coverage exactly as required. This is an open actuarial theorem, derived from realised claim events or their expected values.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.7, general insurance–annuity identity, printed p. 71. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_surv
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_epv
import Definitions.Def_actuarial_c_due
import Definitions.Def_actuarial_c_inc
import Definitions.Def_actuarial_c_increasingDue

open ActuarialAssurances

theorem actuarial_c_increasing_insurance_annuity (h : ℕ) (v : ℝ) (p : ℕ → ℝ) : epv h v inc p+(1-v)*increasingDue h v p+(h : ℝ)*v^h*surv h p h=due h h v p := by sorry
