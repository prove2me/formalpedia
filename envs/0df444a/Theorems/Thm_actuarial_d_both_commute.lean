-- Prove2me | Theorems.Thm_actuarial_d_both_commute
-- name    : actuarial_d_both_commute
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:55:53.057038+00:00
-- url     : https://prove2.me/theorems/5abd944e-e67f-4c4e-9347-447ad3af9f1d
-- title:
--   Joint-life label symmetry
-- statement:
--   Joint-life label symmetry. Both-alive entitlement is unaffected by interchanging the two lives. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   I_{\text{both}}(i,j,t)=I_{\text{both}}(j,i,t)
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

theorem actuarial_d_both_commute (i j t : ℕ) : both i j t = both j i t := by sorry
