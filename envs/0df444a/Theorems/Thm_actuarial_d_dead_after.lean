-- Prove2me | Theorems.Thm_actuarial_d_dead_after
-- name    : actuarial_d_dead_after
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:57:09.895235+00:00
-- url     : https://prove2.me/theorems/c58f4a31-fa58-47bc-a529-4bc6d009eb03
-- title:
--   Dead status at next anniversary
-- statement:
--   Dead status at next anniversary. The recorded death suppresses the following scheduled payment. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   D_x(i,i+1)=1
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.2, p. 144. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_d_dead

open ActuarialJointD

theorem actuarial_d_dead_after (i : ℕ) : dead i (i+1) = 1 := by sorry
