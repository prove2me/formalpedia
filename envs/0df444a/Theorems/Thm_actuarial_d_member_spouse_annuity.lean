-- Prove2me | Theorems.Thm_actuarial_d_member_spouse_annuity
-- name    : actuarial_d_member_spouse_annuity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-13T07:00:47.375693+00:00
-- url     : https://prove2.me/theorems/d196a6e9-4c0b-4298-8eb1-2bf4fd617c09
-- title:
--   Member pension plus reversionary spouse pension
-- statement:
--   Member pension plus reversionary spouse pension. Separate non-overlapping contractual payment streams add linearly. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   V_{\text{member+spouse}}=a_x+\rho a_{y\mid x}
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

theorem actuarial_d_member_spouse_annuity (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) (rho : ℝ) : annMemberSpouse h n p d b rho = annX h n p d b + rho * annRev h n p d b := by sorry
