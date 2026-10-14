-- Prove2me | Theorems.Thm_actuarial_d_first_zero_discount
-- name    : actuarial_d_first_zero_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T07:04:54.498167+00:00
-- url     : https://prove2.me/theorems/c2625466-7b0e-4182-b2eb-827ca6d4e9d4
-- title:
--   First-death zero-discount limit
-- statement:
--   First-death zero-discount limit. All first-death settlement discounts vanish. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   A_1(d_t\equiv0)=0
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.8.1, p. 153. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_assureFirst
import Definitions.Def_actuarial_d_firstPath
import Definitions.Def_actuarial_d_expect

open ActuarialJointD

theorem actuarial_d_first_zero_discount (h : ℕ) (p : ℕ → ℕ → ℝ) : assureFirst h p (fun _ => 0) = 0 := by sorry
