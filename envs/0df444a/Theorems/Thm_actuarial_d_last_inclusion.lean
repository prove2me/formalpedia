-- Prove2me | Theorems.Thm_actuarial_d_last_inclusion
-- name    : actuarial_d_last_inclusion
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:54:47.298983+00:00
-- url     : https://prove2.me/theorems/f7901bf8-fdd5-4dc9-ab86-139247a3d9c1
-- title:
--   Last-survivor inclusion–exclusion
-- statement:
--   Last-survivor inclusion–exclusion. Single-life survivor indicators count both-alive states twice. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   I_{\text{last}}=I_x+I_y-I_{\text{both}}
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

theorem actuarial_d_last_inclusion (i j t : ℕ) : last i j t = alive i t + alive j t - both i j t := by sorry
