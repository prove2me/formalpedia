-- Prove2me | Theorems.Thm_actuarial_d_last_annuity
-- name    : actuarial_d_last_annuity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-13T06:59:53.350683+00:00
-- url     : https://prove2.me/theorems/c076cf34-b2dd-4711-979b-808dd9e00727
-- title:
--   Last-survivor annuity inclusion–exclusion
-- statement:
--   Last-survivor annuity inclusion–exclusion. The last-survivor value is determined by the two marginal annuities and the genuine joint annuity. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   a_{\text{last}}=a_x+a_y-a_{xy}
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

theorem actuarial_d_last_annuity (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) : annLast h n p d b = annX h n p d b + annY h n p d b - annJoint h n p d b := by sorry
