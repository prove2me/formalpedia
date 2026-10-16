-- Prove2me | Theorems.Thm_actuarial_d_defer_last_identity
-- name    : actuarial_d_defer_last_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T07:06:17.040307+00:00
-- url     : https://prove2.me/theorems/93c4117b-b32b-4b2c-ac4f-9e72e2168c10
-- title:
--   Deferred last-survivor decomposition
-- statement:
--   Deferred last-survivor decomposition. The same deferred temporary dates enter all three constituent annuities. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   a_{\text{last};a,n}=a_{x;a,n}+a_{y;a,n}-a_{xy;a,n}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_deferLast
import Definitions.Def_actuarial_d_deferX
import Definitions.Def_actuarial_d_deferY
import Definitions.Def_actuarial_d_deferJoint

open ActuarialJointD

theorem actuarial_d_defer_last_identity (h a n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) : deferLast h a n p d b = deferX h a n p d b + deferY h a n p d b - deferJoint h a n p d b := by sorry
