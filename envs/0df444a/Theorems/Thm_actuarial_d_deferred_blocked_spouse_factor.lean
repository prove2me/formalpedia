-- Prove2me | Theorems.Thm_actuarial_d_deferred_blocked_spouse_factor
-- name    : actuarial_d_deferred_blocked_spouse_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T11:28:29.499738+00:00
-- url     : https://prove2.me/theorems/4be41c47-348b-47b2-8137-fe4e763071d9
-- title:
--   Deferred reversion reduced for a guarantee period
-- statement:
--   Deferred reversion reduced for a guarantee period. The blocked spouse continuation removes eligible payments during the original guaranteed member stream. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   a_R=a_{y\mid x}-a_O
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_deferBlockedRev
import Definitions.Def_actuarial_d_deferRev
import Definitions.Def_actuarial_d_deferOverlap

open ActuarialJointD

theorem actuarial_d_deferred_blocked_spouse_factor (h a n g : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) : deferBlockedRev h a n g p d b = deferRev h a n p d b - deferOverlap h a n g p d b := by sorry
