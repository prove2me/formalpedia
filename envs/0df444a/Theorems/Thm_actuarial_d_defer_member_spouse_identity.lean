-- Prove2me | Theorems.Thm_actuarial_d_defer_member_spouse_identity
-- name    : actuarial_d_defer_member_spouse_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T07:06:59.366983+00:00
-- url     : https://prove2.me/theorems/986c456d-dc1f-496b-bcde-592ee6822ff8
-- title:
--   Deferred member-and-spouse factor
-- statement:
--   Deferred member-and-spouse factor. Additive member and spouse cashflows use the identical deferred period and benefit dates. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   V_{a,n}=a_{x;a,n}+\rho a_{y\mid x;a,n}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_deferMemberSpouse
import Definitions.Def_actuarial_d_deferX
import Definitions.Def_actuarial_d_deferRev

open ActuarialJointD

theorem actuarial_d_defer_member_spouse_identity (h a n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) (rho : ℝ) : deferMemberSpouse h a n p d b rho = deferX h a n p d b + rho * deferRev h a n p d b := by sorry
