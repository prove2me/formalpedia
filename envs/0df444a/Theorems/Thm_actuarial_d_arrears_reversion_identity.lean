-- Prove2me | Theorems.Thm_actuarial_d_arrears_reversion_identity
-- name    : actuarial_d_arrears_reversion_identity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-13T07:07:52.889265+00:00
-- url     : https://prove2.me/theorems/464e9f10-cd45-4c81-9a5b-24415011b0e2
-- title:
--   Arrears reversionary identity
-- statement:
--   Arrears reversionary identity. Member-death/spouse-survival status governs the instalment at the end of each period. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   a_{y\mid x}^{\text{arrears}}=a_y^{\text{arrears}}-a_{xy}^{\text{arrears}}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_arrearsRev
import Definitions.Def_actuarial_d_arrearsY
import Definitions.Def_actuarial_d_arrearsJoint

open ActuarialJointD

theorem actuarial_d_arrears_reversion_identity (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) : arrearsRev h n p d b = arrearsY h n p d b - arrearsJoint h n p d b := by sorry
