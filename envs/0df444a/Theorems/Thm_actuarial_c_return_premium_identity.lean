-- Prove2me | Theorems.Thm_actuarial_c_return_premium_identity
-- name    : actuarial_c_return_premium_identity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T21:28:25.507983+00:00
-- url     : https://prove2.me/theorems/72bc23cf-b5e8-449d-8f72-f6f2a0026c60
-- title:
--   Returning premiums without interest on death is an increasing death assurance
-- statement:
--   Returning premiums without interest on death is an increasing death assurance.
--
--   Mathematical relation:
--
--   $$
--   A^{\text{return}}(P)=P A^{\uparrow}
--   $$
--
--   The declared assumptions restrict the life law, discount and coverage exactly as required. This is an open actuarial theorem, derived from realised claim events or their expected values.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.2, net premium ratio and premium stream, printed p. 63. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_epv
import Definitions.Def_actuarial_c_inc
import Definitions.Def_actuarial_c_returnBenefits

open ActuarialAssurances

theorem actuarial_c_return_premium_identity (h : ℕ) (v premium : ℝ) (p : ℕ → ℝ) : epv h v (returnBenefits premium) p=premium*epv h v inc p := by sorry
