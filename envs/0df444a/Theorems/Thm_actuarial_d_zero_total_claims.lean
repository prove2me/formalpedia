-- Prove2me | Theorems.Thm_actuarial_d_zero_total_claims
-- name    : actuarial_d_zero_total_claims
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T07:05:36.12424+00:00
-- url     : https://prove2.me/theorems/54a20502-4de1-46b5-856c-f810761dfd07
-- title:
--   Annuity-only reduction
-- statement:
--   Annuity-only reduction. Suppressing all death riders leaves the member-and-spouse annuity from the same joint law. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   V_{\text{total};f=s=f_x=f_y=f_t=0}=a_x+\rho a_{y\mid x}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_totalValue
import Definitions.Def_actuarial_d_totalPath
import Definitions.Def_actuarial_d_annMemberSpouse
import Definitions.Def_actuarial_d_expect

open ActuarialJointD

theorem actuarial_d_zero_total_claims (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) (rho : ℝ) : totalValue h n p d b rho 0 0 0 0 0 = annMemberSpouse h n p d b rho := by sorry
