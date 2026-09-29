-- Prove2me | Theorems.Thm_mme_entropy_le_cross_entropy
-- name    : mme_entropy_le_cross_entropy
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T06:22:08.542217+00:00
-- url     : https://prove2.me/theorems/0a2bf124-66b2-4e7c-b689-a92297581361
-- title:
--   Cross entropy bounds entropy for a subprobability comparison
-- statement:
--   For finite probability distributions, a nonnegative comparison function of total mass at most one bounds entropy by cross entropy whenever it is positive on the probability support. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Definitions.Def_mme_regional_entropy_rate_data
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
open scoped BigOperators
open MME.RegionRate

theorem mme_entropy_le_cross_entropy {W : Type*} [Fintype W]
    (p q : W → ℝ) (hp : ∀ w, 0 ≤ p w) (hq : ∀ w, 0 ≤ q w)
    (hmass : ∑ w, p w = 1) (hqmass : ∑ w, q w ≤ 1)
    (hsupport : ∀ w, 0 < p w → 0 < q w) :
    entropy p ≤ -∑ w, p w * Real.log (q w) := by sorry
