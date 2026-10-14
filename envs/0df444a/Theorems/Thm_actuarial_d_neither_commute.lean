-- Prove2me | Theorems.Thm_actuarial_d_neither_commute
-- name    : actuarial_d_neither_commute
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:56:11.081751+00:00
-- url     : https://prove2.me/theorems/e41f6914-25d5-4d78-8498-d86bef7d20e8
-- title:
--   Both-dead label symmetry
-- statement:
--   Both-dead label symmetry. The completely extinguished state is symmetric in lives. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   I_{\text{neither}}(i,j,t)=I_{\text{neither}}(j,i,t)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.2, p. 144. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_d_dead
import Definitions.Def_actuarial_d_both
import Definitions.Def_actuarial_d_onlyX
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_neither
import Definitions.Def_actuarial_d_last

open ActuarialJointD

theorem actuarial_d_neither_commute (i j t : ℕ) : neither i j t = neither j i t := by sorry
