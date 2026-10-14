-- Prove2me | Theorems.Thm_actuarial_d_last_partition
-- name    : actuarial_d_last_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:54:33.162976+00:00
-- url     : https://prove2.me/theorems/d1eba32e-401a-4279-ad23-738df3e7ff0b
-- title:
--   Last-survivor state partition
-- statement:
--   Last-survivor state partition. A last-survivor payment is due in precisely the three live states. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   I_{\text{last}}=I_{\text{both}}+I_{\text{x only}}+I_{\text{y only}}
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

theorem actuarial_d_last_partition (i j t : ℕ) : last i j t = both i j t + onlyX i j t + onlyY i j t := by sorry
