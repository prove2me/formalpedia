-- Prove2me | Theorems.Thm_actuarial_c_level_insurance_annuity_unnormalised
-- name    : actuarial_c_level_insurance_annuity_unnormalised
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T21:30:01.017391+00:00
-- url     : https://prove2.me/theorems/1cba6307-7cb9-4eb8-af13-6bf00885e595
-- title:
--   Annual level-insurance identity works before imposing unit total probability
-- statement:
--   Annual level-insurance identity works before imposing unit total probability.
--
--   Mathematical relation:
--
--   $$
--   A(1)+(1-v)\ddot a_h+v^hS(h)=\sum_{j=0}^{h}p_j
--   $$
--
--   The declared assumptions restrict the life law, discount and coverage exactly as required. This is an open actuarial theorem, derived from realised claim events or their expected values.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.7, general insurance–annuity identity, printed p. 71. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_total
import Definitions.Def_actuarial_c_surv
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_epv
import Definitions.Def_actuarial_c_due

open ActuarialAssurances

theorem actuarial_c_level_insurance_annuity_unnormalised (h : ℕ) (v : ℝ) (p : ℕ → ℝ) : epv h v (fun _ => 1) p+(1-v)*due h h v p+v^h*surv h p h=total h p := by sorry
