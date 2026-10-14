-- Prove2me | Theorems.Thm_actuarial_d_reversion_complement
-- name    : actuarial_d_reversion_complement
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:54:57.763792+00:00
-- url     : https://prove2.me/theorems/0d4d2301-015f-4c2d-925c-18c0f102be7d
-- title:
--   Reversionary state difference
-- statement:
--   Reversionary state difference. The reversionary benefit excludes overlap while the member remains alive. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   I_{\text{y only}}=I_y-I_{\text{both}}
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

theorem actuarial_d_reversion_complement (i j t : ℕ) : onlyY i j t = alive j t - both i j t := by sorry
