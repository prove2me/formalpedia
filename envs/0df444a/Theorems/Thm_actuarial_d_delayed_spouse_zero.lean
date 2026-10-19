-- Prove2me | Theorems.Thm_actuarial_d_delayed_spouse_zero
-- name    : actuarial_d_delayed_spouse_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T11:02:54.572563+00:00
-- url     : https://prove2.me/theorems/8521be98-b129-4154-bb36-d27308c063d7
-- title:
--   Zero-guarantee spouse commencement
-- statement:
--   Zero-guarantee spouse commencement. Without a guarantee the spouse entitlement begins at member death, subject to survival. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   R_{0}(t)=I_{y\mid x}(t)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_delayedSpouse
import Definitions.Def_actuarial_d_onlyY

open ActuarialJointD

theorem actuarial_d_delayed_spouse_zero (i j t : ℕ) : delayedSpouse 0 i j t = onlyY i j t := by sorry
