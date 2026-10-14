-- Prove2me | Theorems.Thm_actuarial_d_x_first_swap
-- name    : actuarial_d_x_first_swap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:58:23.388795+00:00
-- url     : https://prove2.me/theorems/cd174337-3cc9-4033-9cc4-bf4cc4f8fcdd
-- title:
--   Contingent first-death label exchange
-- statement:
--   Contingent first-death label exchange. Swapping lives switches which first-death contingency is eligible. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   C_{x\prec y}(i,j)=C_{y\prec x}(j,i)
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

theorem actuarial_d_x_first_swap (h i j : ℕ) (d : ℕ → ℝ) : xFirstPath h d i j = yFirstPath h d j i := by sorry
