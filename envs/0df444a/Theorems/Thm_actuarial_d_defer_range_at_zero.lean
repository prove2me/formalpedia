-- Prove2me | Theorems.Thm_actuarial_d_defer_range_at_zero
-- name    : actuarial_d_defer_range_at_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T07:05:57.276977+00:00
-- url     : https://prove2.me/theorems/e91d51b5-cd65-4e66-9131-58a175e00ba5
-- title:
--   Undeferred annuity recovery
-- statement:
--   Undeferred annuity recovery. A deferred annuity beginning at issue reduces exactly to the ordinary due-annuity cashflow. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   Z_{0,n}=Z_n
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_annRange
import Definitions.Def_actuarial_d_annPath

open ActuarialJointD

theorem actuarial_d_defer_range_at_zero (n : ℕ) (d b s : ℕ → ℝ) : annRange 0 n d b s = annPath n d b s := by sorry
