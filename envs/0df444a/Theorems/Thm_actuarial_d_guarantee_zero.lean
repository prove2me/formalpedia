-- Prove2me | Theorems.Thm_actuarial_d_guarantee_zero
-- name    : actuarial_d_guarantee_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T11:02:45.300841+00:00
-- url     : https://prove2.me/theorems/163b290f-e279-4519-89f5-06f376a18c06
-- title:
--   Zero-guarantee member status
-- statement:
--   Zero-guarantee member status. At zero guaranteed duration a pension payment requires member survival. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   G_{0}(t)=I_x(t)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_guaranteeMember
import Definitions.Def_actuarial_d_alive

open ActuarialJointD

theorem actuarial_d_guarantee_zero (i t : ℕ) : guaranteeMember 0 i t = alive i t := by sorry
