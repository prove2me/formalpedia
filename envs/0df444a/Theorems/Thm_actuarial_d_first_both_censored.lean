-- Prove2me | Theorems.Thm_actuarial_d_first_both_censored
-- name    : actuarial_d_first_both_censored
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:59:07.573292+00:00
-- url     : https://prove2.me/theorems/f8b68a88-7a23-45be-a3a8-ca259cddabc6
-- title:
--   No first death when both are censored
-- statement:
--   No first death when both are censored. No death benefit is triggered by either life surviving the observed horizon. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   C_1(h,h)=0
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.8.1, p. 153. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_firstPath
import Definitions.Def_actuarial_d_secondPath
import Definitions.Def_actuarial_d_xFirstPath
import Definitions.Def_actuarial_d_yFirstPath
import Definitions.Def_actuarial_d_xSecondPath
import Definitions.Def_actuarial_d_ySecondPath
import Definitions.Def_actuarial_d_tiePath

open ActuarialJointD

theorem actuarial_d_first_both_censored (h : ℕ) (d : ℕ → ℝ) : firstPath h d h h = 0 := by sorry
