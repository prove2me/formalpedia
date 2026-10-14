-- Prove2me | Theorems.Thm_actuarial_d_second_spouse_censored
-- name    : actuarial_d_second_spouse_censored
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:59:33.195679+00:00
-- url     : https://prove2.me/theorems/e88d563f-ae42-4593-82aa-169ff30b7647
-- title:
--   No second death when spouse is censored
-- statement:
--   No second death when spouse is censored. An observed first death alone is insufficient to settle second-death assurance. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   C_2(i,h)=0
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

theorem actuarial_d_second_spouse_censored (h i : ℕ) (d : ℕ → ℝ) : secondPath h d i h = 0 := by sorry
