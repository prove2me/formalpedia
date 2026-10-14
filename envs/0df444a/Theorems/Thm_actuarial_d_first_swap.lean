-- Prove2me | Theorems.Thm_actuarial_d_first_swap
-- name    : actuarial_d_first_swap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:57:55.187823+00:00
-- url     : https://prove2.me/theorems/c9851423-8548-4b72-bae9-3d3687406816
-- title:
--   First-death symmetry
-- statement:
--   First-death symmetry. First-death settlement timing is symmetric even with dependent mortality. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   C_1(i,j)=C_1(j,i)
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

theorem actuarial_d_first_swap (h i j : ℕ) (d : ℕ → ℝ) : firstPath h d i j = firstPath h d j i := by sorry
