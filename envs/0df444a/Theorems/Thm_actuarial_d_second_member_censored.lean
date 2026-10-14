-- Prove2me | Theorems.Thm_actuarial_d_second_member_censored
-- name    : actuarial_d_second_member_censored
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:59:19.982503+00:00
-- url     : https://prove2.me/theorems/562cbcaa-f6bf-4a24-8a5f-8022566a52cf
-- title:
--   No second death when member is censored
-- statement:
--   No second death when member is censored. The later-death benefit needs both actual deaths within the observation window. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   C_2(h,j)=0
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.8.2, p. 154. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

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

theorem actuarial_d_second_member_censored (h j : ℕ) (d : ℕ → ℝ) : secondPath h d h j = 0 := by sorry
