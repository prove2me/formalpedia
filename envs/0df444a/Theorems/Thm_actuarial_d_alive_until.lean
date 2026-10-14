-- Prove2me | Theorems.Thm_actuarial_d_alive_until
-- name    : actuarial_d_alive_until
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:56:54.453416+00:00
-- url     : https://prove2.me/theorems/532275d0-5698-4ea5-b332-c8d7cfda0908
-- title:
--   Last due payment preceding death
-- statement:
--   Last due payment preceding death. A due instalment at the beginning of the recorded death year remains payable. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   I_x(i,i)=1
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.2, p. 144. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_d_dead

open ActuarialJointD

theorem actuarial_d_alive_until (i : ℕ) : alive i i = 1 := by sorry
