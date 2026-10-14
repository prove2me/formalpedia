-- Prove2me | Theorems.Thm_actuarial_d_state_partition
-- name    : actuarial_d_state_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:53:37.358638+00:00
-- url     : https://prove2.me/theorems/c7da9c84-e5dd-4b87-8a36-e0cbc79c9de0
-- title:
--   Four outcome mass conservation
-- statement:
--   Four outcome mass conservation. The four mutually exclusive survivor states exhaust every joint outcome. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   I_{\text{both}}+I_{\text{x only}}+I_{\text{y only}}+I_{\text{neither}}=1
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

theorem actuarial_d_state_partition (i j t : ℕ) : both i j t + onlyX i j t + onlyY i j t + neither i j t = 1 := by sorry
