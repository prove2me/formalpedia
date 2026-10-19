-- Prove2me | Theorems.Thm_actuarial_d_mthly_zero_years
-- name    : actuarial_d_mthly_zero_years
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T11:02:21.590478+00:00
-- url     : https://prove2.me/theorems/78b95f28-b00a-46d3-a838-85d3ec2692da
-- title:
--   Empty subannual term
-- statement:
--   Empty subannual term. There are no payment ticks when the duration is zero, whatever the instalment frequency. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   Z^{(m)}_{y=0}=0
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_mthlyPath

open ActuarialJointD

theorem actuarial_d_mthly_zero_years (m : ℕ) (d b s : ℕ → ℝ) : mthlyPath 0 m d b s = 0 := by sorry
