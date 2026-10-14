-- Prove2me | Theorems.Thm_actuarial_d_arrears_zero_term
-- name    : actuarial_d_arrears_zero_term
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T07:08:07.871691+00:00
-- url     : https://prove2.me/theorems/b3b11137-185d-4172-8e85-a3734968c62e
-- title:
--   Empty annuity-arrears term
-- statement:
--   Empty annuity-arrears term. No end-of-period instalment exists when the contract term has zero periods. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   a_{\text{last};n=0}^{\text{arrears}}=0
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_arrearsLast

open ActuarialJointD

theorem actuarial_d_arrears_zero_term (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) : arrearsLast h 0 p d b = 0 := by sorry
