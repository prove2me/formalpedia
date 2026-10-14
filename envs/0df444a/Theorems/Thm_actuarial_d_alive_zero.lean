-- Prove2me | Theorems.Thm_actuarial_d_alive_zero
-- name    : actuarial_d_alive_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:56:34.642197+00:00
-- url     : https://prove2.me/theorems/b6f17abd-ddfb-40aa-8580-bf3c758fcf57
-- title:
--   Commencement survival with nonnegative death year
-- statement:
--   Commencement survival with nonnegative death year. An initial life with first-death year nonnegative is alive at issue under this model. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   I_x(i,0)=1
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.2, p. 144. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_d_dead

open ActuarialJointD

theorem actuarial_d_alive_zero (i : ℕ) : alive i 0 = 1 := by sorry
