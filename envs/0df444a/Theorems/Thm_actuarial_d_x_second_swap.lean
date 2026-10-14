-- Prove2me | Theorems.Thm_actuarial_d_x_second_swap
-- name    : actuarial_d_x_second_swap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:58:38.412282+00:00
-- url     : https://prove2.me/theorems/7ffe0417-6c0b-4d38-bd24-66d987962ee4
-- title:
--   Contingent second-death label exchange
-- statement:
--   Contingent second-death label exchange. The second-death order payment swaps with the life label. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   C_{x\succ y}(i,j)=C_{y\succ x}(j,i)
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

theorem actuarial_d_x_second_swap (h i j : ℕ) (d : ℕ → ℝ) : xSecondPath h d i j = ySecondPath h d j i := by sorry
