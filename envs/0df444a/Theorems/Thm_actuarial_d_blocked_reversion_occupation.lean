-- Prove2me | Theorems.Thm_actuarial_d_blocked_reversion_occupation
-- name    : actuarial_d_blocked_reversion_occupation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T11:27:57.932906+00:00
-- url     : https://prove2.me/theorems/ddf378c6-9617-48ed-bb34-3a9bd345656f
-- title:
--   Spouse reversion minus guaranteed-window overlap
-- statement:
--   Spouse reversion minus guaranteed-window overlap. Spouse-only dates inside the guaranteed period are excluded from delayed entitlement. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   R(t)=I_{y\mid x}(t)-O(t)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_delayedSpouse
import Definitions.Def_actuarial_d_onlyY

open ActuarialJointD

theorem actuarial_d_blocked_reversion_occupation (g i j t : ℕ) : delayedSpouse g i j t = onlyY i j t - (if t < g then onlyY i j t else 0) := by sorry
