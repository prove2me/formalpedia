-- Prove2me | Theorems.Thm_actuarial_d_mthly_zero_frequency
-- name    : actuarial_d_mthly_zero_frequency
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T11:02:34.021022+00:00
-- url     : https://prove2.me/theorems/92df1177-fe3f-4572-a608-18a78b8e8ea4
-- title:
--   Zero-frequency sentinel convention
-- statement:
--   Zero-frequency sentinel convention. The formal zero frequency is an empty sum; physical contracts require m positive. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   Z^{(m=0)}=0\quad\text{(empty sum)}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_mthlyPath

open ActuarialJointD

theorem actuarial_d_mthly_zero_frequency (years : ℕ) (d b s : ℕ → ℝ) : mthlyPath years 0 d b s = 0 := by sorry
