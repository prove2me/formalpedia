-- Prove2me | Theorems.Thm_actuarial_d_rev_zero_dates
-- name    : actuarial_d_rev_zero_dates
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T07:02:34.48887+00:00
-- url     : https://prove2.me/theorems/5dbbac79-a62c-4390-a1bc-ac98275f6e48
-- title:
--   Empty reversionary payment schedule
-- statement:
--   Empty reversionary payment schedule. There is no reversionary payment before the first possible scheduled instalment. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   a_{y\mid x;n=0}=0
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

theorem actuarial_d_rev_zero_dates (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) : annRev h 0 p d b = 0 := by sorry
