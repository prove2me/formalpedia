-- Prove2me | Theorems.Thm_actuarial_d_second_swap
-- name    : actuarial_d_second_swap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:58:08.46119+00:00
-- url     : https://prove2.me/theorems/8a2cf37a-e623-4763-a07f-c39557f03f08
-- title:
--   Second-death symmetry
-- statement:
--   Second-death symmetry. Second-death settlement timing depends on the later death irrespective of life labels. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   C_2(i,j)=C_2(j,i)
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

theorem actuarial_d_second_swap (h i j : ℕ) (d : ℕ → ℝ) : secondPath h d i j = secondPath h d j i := by sorry
