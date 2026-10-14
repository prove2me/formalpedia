-- Prove2me | Theorems.Thm_actuarial_d_dead_complement
-- name    : actuarial_d_dead_complement
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:55:40.768284+00:00
-- url     : https://prove2.me/theorems/db010e38-7783-411e-9800-3116dbbf6a74
-- title:
--   Alive/dead conservation
-- statement:
--   Alive/dead conservation. The same death-year state cannot be both alive and dead at a payment anniversary. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   I_{\text{dead}}+I_{\text{alive}}=1
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

theorem actuarial_d_dead_complement (i j t : ℕ) : dead i t + alive i t = 1 := by sorry
