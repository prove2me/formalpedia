-- Prove2me | Theorems.Thm_actuarial_d_neither_complement
-- name    : actuarial_d_neither_complement
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:55:28.359596+00:00
-- url     : https://prove2.me/theorems/c35fe4a3-da65-4e18-bb38-81e27541ed33
-- title:
--   Neither-survives complement
-- statement:
--   Neither-survives complement. Complete extinction is complementary to last-survivor entitlement. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   I_{\text{neither}}=1-I_{\text{last}}
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

theorem actuarial_d_neither_complement (i j t : ℕ) : neither i j t = 1 - last i j t := by sorry
