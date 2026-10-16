-- Prove2me | Theorems.Thm_actuarial_d_member_spouse_last
-- name    : actuarial_d_member_spouse_last
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T07:01:04.271171+00:00
-- url     : https://prove2.me/theorems/9eb96695-4498-46ae-8f04-9da171a9427f
-- title:
--   Member-plus-survivor alternative decomposition
-- statement:
--   Member-plus-survivor alternative decomposition. The same pension stream is a weighted member annuity plus a last-survivor annuity. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   V_{\text{member+spouse}}=(1-\rho)a_x+\rho a_{\text{last}}
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

theorem actuarial_d_member_spouse_last (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) (rho : ℝ) : annMemberSpouse h n p d b rho = (1-rho) * annX h n p d b + rho * annLast h n p d b := by sorry
