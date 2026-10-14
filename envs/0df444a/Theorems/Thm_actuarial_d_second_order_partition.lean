-- Prove2me | Theorems.Thm_actuarial_d_second_order_partition
-- name    : actuarial_d_second_order_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:57:42.13956+00:00
-- url     : https://prove2.me/theorems/1e5f4ea6-ed75-4a5f-810b-2b3bcdbe3918
-- title:
--   Second-death order and tie partition
-- statement:
--   Second-death order and tie partition. The second claim allocates to the later death or simultaneous death, when both deaths are observed. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   C_2=C_{x\succ y}^{(2)}+C_{y\succ x}^{(2)}+C_{\text{tie}}
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

theorem actuarial_d_second_order_partition (h i j : ℕ) (d : ℕ → ℝ) : secondPath h d i j = xSecondPath h d i j + ySecondPath h d i j + tiePath h d i j := by sorry
