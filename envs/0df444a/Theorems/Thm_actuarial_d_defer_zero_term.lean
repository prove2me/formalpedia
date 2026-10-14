-- Prove2me | Theorems.Thm_actuarial_d_defer_zero_term
-- name    : actuarial_d_defer_zero_term
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T07:07:16.873095+00:00
-- url     : https://prove2.me/theorems/9646652b-8f68-439f-917f-a76c75c6b8b6
-- title:
--   Zero-duration deferred survivor annuity
-- statement:
--   Zero-duration deferred survivor annuity. No deferred instalment exists if the temporary period has length zero. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   a_{\text{last};a,0}=0
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_deferLast

open ActuarialJointD

theorem actuarial_d_defer_zero_term (h a n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) : deferLast h a 0 p d b = 0 := by sorry
