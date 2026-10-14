-- Prove2me | Theorems.Thm_actuarial_d_second_zero_discount
-- name    : actuarial_d_second_zero_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T07:05:19.926333+00:00
-- url     : https://prove2.me/theorems/7e04ff49-5b43-4165-af70-347c8838baf8
-- title:
--   Second-death zero-discount limit
-- statement:
--   Second-death zero-discount limit. All second-death settlement discounts vanish. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   A_2(d_t\equiv0)=0
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.8.2, p. 154. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_assureSecond
import Definitions.Def_actuarial_d_secondPath
import Definitions.Def_actuarial_d_expect

open ActuarialJointD

theorem actuarial_d_second_zero_discount (h : ℕ) (p : ℕ → ℕ → ℝ) : assureSecond h p (fun _ => 0) = 0 := by sorry
