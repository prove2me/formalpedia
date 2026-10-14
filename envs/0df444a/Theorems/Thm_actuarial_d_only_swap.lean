-- Prove2me | Theorems.Thm_actuarial_d_only_swap
-- name    : actuarial_d_only_swap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:56:25.856627+00:00
-- url     : https://prove2.me/theorems/ae910480-96a4-4fdf-9b58-3dcca12f6b80
-- title:
--   Reversionary status label exchange
-- statement:
--   Reversionary status label exchange. Swapping member and spouse exchanges the two single-survivor states. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   I_{\text{y only}}(i,j,t)=I_{\text{x only}}(j,i,t)
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

theorem actuarial_d_only_swap (i j t : ℕ) : onlyY i j t = onlyX j i t := by sorry
