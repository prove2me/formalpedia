-- Prove2me | Theorems.Thm_actuarial_d_arrears_last_identity
-- name    : actuarial_d_arrears_last_identity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-13T07:07:37.657985+00:00
-- url     : https://prove2.me/theorems/42cd870a-8da3-43a7-be45-b5289028e4e4
-- title:
--   Arrears last-survivor relation
-- statement:
--   Arrears last-survivor relation. Survivor status is checked at every end-of-period payment date. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   a_{\text{last}}^{\text{arrears}}=a_x^{\text{arrears}}+a_y^{\text{arrears}}-a_{xy}^{\text{arrears}}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_arrearsLast
import Definitions.Def_actuarial_d_arrearsX
import Definitions.Def_actuarial_d_arrearsY
import Definitions.Def_actuarial_d_arrearsJoint

open ActuarialJointD

theorem actuarial_d_arrears_last_identity (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) : arrearsLast h n p d b = arrearsX h n p d b + arrearsY h n p d b - arrearsJoint h n p d b := by sorry
