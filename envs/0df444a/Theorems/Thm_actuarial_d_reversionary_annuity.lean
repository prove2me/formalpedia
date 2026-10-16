-- Prove2me | Theorems.Thm_actuarial_d_reversionary_annuity
-- name    : actuarial_d_reversionary_annuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T07:00:30.097983+00:00
-- url     : https://prove2.me/theorems/f7bc1cea-a526-4f94-9541-bdea1de324cc
-- title:
--   Spouse reversionary identity
-- statement:
--   Spouse reversionary identity. Spouse-only payments exclude all dates when the member is also alive. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   a_{y\mid x}=a_y-a_{xy}
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

theorem actuarial_d_reversionary_annuity (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) : annRev h n p d b = annY h n p d b - annJoint h n p d b := by sorry
