-- Prove2me | Theorems.Thm_actuarial_d_alive_after
-- name    : actuarial_d_alive_after
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:56:44.385422+00:00
-- url     : https://prove2.me/theorems/7c8c6f15-99ac-4f7c-895d-3cc6a6ad7898
-- title:
--   First unpaid anniversary following death
-- statement:
--   First unpaid anniversary following death. No life annuity payment is made at the anniversary after its recorded death-year index. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   I_x(i,i+1)=0
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.2, p. 144. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_d_dead

open ActuarialJointD

theorem actuarial_d_alive_after (i : ℕ) : alive i (i+1) = 0 := by sorry
