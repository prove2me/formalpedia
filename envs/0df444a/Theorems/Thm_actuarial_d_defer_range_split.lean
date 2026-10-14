-- Prove2me | Theorems.Thm_actuarial_d_defer_range_split
-- name    : actuarial_d_defer_range_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T07:05:47.163182+00:00
-- url     : https://prove2.me/theorems/9fd80e2c-f91a-4e7e-85d0-49b0a79cca41
-- title:
--   Temporary annuity term splitting
-- statement:
--   Temporary annuity term splitting. Payment intervals are disjoint and consecutive even when the first payment is deferred. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   Z_{a,n+m}=Z_{a,n}+Z_{a+n,m}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_annRange

open ActuarialJointD

theorem actuarial_d_defer_range_split (a n m : ℕ) (d b s : ℕ → ℝ) : annRange a (n+m) d b s = annRange a n d b s + annRange (a+n) m d b s := by sorry
