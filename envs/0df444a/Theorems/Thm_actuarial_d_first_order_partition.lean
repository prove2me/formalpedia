-- Prove2me | Theorems.Thm_actuarial_d_first_order_partition
-- name    : actuarial_d_first_order_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:57:30.245206+00:00
-- url     : https://prove2.me/theorems/37faeda8-5a8d-44f1-aa0a-e997c71b50de
-- title:
--   First-death order and tie partition
-- statement:
--   First-death order and tie partition. The first claim is allocated exactly once across member-first, spouse-first and tied deaths. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   C_1=C_{x\prec y}^{(1)}+C_{y\prec x}^{(1)}+C_{\text{tie}}
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

theorem actuarial_d_first_order_partition (h i j : ℕ) (d : ℕ → ℝ) : firstPath h d i j = xFirstPath h d i j + yFirstPath h d i j + tiePath h d i j := by sorry
