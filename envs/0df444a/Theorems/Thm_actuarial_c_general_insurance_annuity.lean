-- Prove2me | Theorems.Thm_actuarial_c_general_insurance_annuity
-- name    : actuarial_c_general_insurance_annuity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T21:29:26.072982+00:00
-- url     : https://prove2.me/theorems/81a1acc0-1e27-485a-9bbc-f63e2a7322f0
-- title:
--   Discrete integration by parts links any death-benefit vector to survivor annuities and a terminal boundary correction
-- statement:
--   Discrete integration by parts links any death-benefit vector to survivor annuities and a terminal boundary correction.
--
--   Mathematical relation:
--
--   $$
--   A(b)+(1-v)\ddot a(b)+v^hb_{h-1}S(h)=b_0S(0)+\sum_{j=1}^{h-1}v^j(b_j-b_{j-1})S(j)
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
import Definitions.Def_actuarial_c_weightedDue
import Definitions.Def_actuarial_c_differenceBenefit

open ActuarialAssurances

theorem actuarial_c_general_insurance_annuity (h : ℕ) (v : ℝ) (b p : ℕ → ℝ) : epv h v b p+(1-v)*weightedDue h v b p+v^h*b (h-1)*surv h p h=differenceBenefit h v b p := by sorry
