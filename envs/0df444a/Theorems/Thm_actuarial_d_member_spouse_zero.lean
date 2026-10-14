-- Prove2me | Theorems.Thm_actuarial_d_member_spouse_zero
-- name    : actuarial_d_member_spouse_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T07:01:22.755962+00:00
-- url     : https://prove2.me/theorems/11696b1d-5276-4ba6-ba13-bfc25f890a5e
-- title:
--   No spouse continuation
-- statement:
--   No spouse continuation. A zero spouse percentage recovers the member-only annuity. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   V_{\rho=0}=a_x
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_annValue
import Definitions.Def_actuarial_d_annPath
import Definitions.Def_actuarial_d_annX
import Definitions.Def_actuarial_d_annY
import Definitions.Def_actuarial_d_annJoint
import Definitions.Def_actuarial_d_annLast
import Definitions.Def_actuarial_d_annRev
import Definitions.Def_actuarial_d_annMemberSpouse

open ActuarialJointD

theorem actuarial_d_member_spouse_zero (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) : annMemberSpouse h n p d b 0 = annX h n p d b := by sorry
