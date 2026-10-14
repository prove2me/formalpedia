-- Prove2me | Theorems.Thm_actuarial_d_defer_reversion_identity
-- name    : actuarial_d_defer_reversion_identity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-13T07:06:35.803774+00:00
-- url     : https://prove2.me/theorems/9a31a908-3d07-48b8-92dc-a5a58a4ed724
-- title:
--   Deferred spouse reversion
-- statement:
--   Deferred spouse reversion. The surviving spouse receives only dates when the member has already died. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   a_{y\mid x;a,n}=a_{y;a,n}-a_{xy;a,n}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_deferRev
import Definitions.Def_actuarial_d_deferY
import Definitions.Def_actuarial_d_deferJoint

open ActuarialJointD

theorem actuarial_d_defer_reversion_identity (h a n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) : deferRev h a n p d b = deferY h a n p d b - deferJoint h a n p d b := by sorry
