-- Prove2me | Theorems.Thm_actuarial_d_guarantee_topup_occupation
-- name    : actuarial_d_guarantee_topup_occupation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T11:09:13.072525+00:00
-- url     : https://prove2.me/theorems/01551cbe-20ae-4162-b395-75a3d3e069d8
-- title:
--   Guaranteed pension equals ordinary member plus top-up
-- statement:
--   Guaranteed pension equals ordinary member plus top-up. Guarantee cashflow beyond member death can be isolated without double-counting live member dates. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   G(t)=I_x(t)+U(t)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_guaranteeMember
import Definitions.Def_actuarial_d_guaranteeTopup
import Definitions.Def_actuarial_d_alive

open ActuarialJointD

theorem actuarial_d_guarantee_topup_occupation (g i t : ℕ) : guaranteeMember g i t = alive i t + guaranteeTopup g i t := by sorry
