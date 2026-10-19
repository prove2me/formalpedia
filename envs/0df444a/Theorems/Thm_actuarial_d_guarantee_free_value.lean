-- Prove2me | Theorems.Thm_actuarial_d_guarantee_free_value
-- name    : actuarial_d_guarantee_free_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T11:03:41.784689+00:00
-- url     : https://prove2.me/theorems/682b40c5-7a2e-4d6c-b718-b55177dafcb4
-- title:
--   Zero-guarantee pension factor
-- statement:
--   Zero-guarantee pension factor. In the absence of guaranteed payments the ordinary member-and-spouse status applies. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   V_{g=0}=a_x+\rho a_{y\mid x}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_guaranteeDelayValue
import Definitions.Def_actuarial_d_annMemberSpouse

open ActuarialJointD

theorem actuarial_d_guarantee_free_value (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) (rho : ℝ) : guaranteeDelayValue h n 0 p d b rho = annMemberSpouse h n p d b rho := by sorry
