-- Prove2me | Theorems.Thm_actuarial_c_mass_cohort_decrement
-- name    : actuarial_c_mass_cohort_decrement
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:31:58.706981+00:00
-- url     : https://prove2.me/theorems/f124b042-53e2-435f-bdf4-489418cfefff
-- title:
--   The survivor-tail cohort decreases by exactly the corresponding death-year probability
-- statement:
--   The survivor-tail cohort decreases by exactly the corresponding death-year probability.
--
--   Mathematical relation:
--
--   $$
--   S(j)-S(j+1)=p_j,\quad j<h
--   $$
--
--   The declared assumptions restrict the life law, discount and coverage exactly as required. This is an open actuarial theorem, derived from realised claim events or their expected values.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.7, general identity and actuarial notation, printed p. 71. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_surv
import Definitions.Def_actuarial_c_massCohort

open ActuarialAssurances

theorem actuarial_c_mass_cohort_decrement (h j : ℕ) (p : ℕ → ℝ) (hj : j < h) : massCohort h p j-massCohort h p (j+1)=p j := by sorry
