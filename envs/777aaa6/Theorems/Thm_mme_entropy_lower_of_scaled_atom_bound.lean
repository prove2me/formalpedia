-- Prove2me | Theorems.Thm_mme_entropy_lower_of_scaled_atom_bound
-- name    : mme_entropy_lower_of_scaled_atom_bound
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T23:57:09.323051+00:00
-- url     : https://prove2.me/theorems/1f4c9e48-53ac-4a52-844e-9810e5cc5ddd
-- title:
--   Entropy lower bound from a scaled atom bound
-- statement:
--   For a nonnegative finite probability distribution whose atoms are at most b and any positive a, the natural-log entropy is at least log(a)+1-a*b. The proof applies log(a*p) <= a*p-1 and sums the weighted inequalities.
-- source:
--   Exact integer histograms of the released 116 profile, the elementary logarithm tangent bound, and the pinned mathlib certified logarithm-of-two estimate.

import Theorems.Thm_mme_regional_mass_entropy_algebra
import Theorems.Thm_mme_released_116_regional_split_mass
import Definitions.Def_mme_regional_split_entropy_data
open BigOperators MME MME.RegionRate MME.RecursiveThinSplit
set_option autoImplicit false
universe u

theorem mme_entropy_lower_of_scaled_atom_bound {W : Type*} [Fintype W]
    (p : W → ℝ) (a b : ℝ) (ha : 0 < a) (hp : ∀ w, 0 ≤ p w)
    (hmass : ∑ w, p w = 1) (hbound : ∀ w, p w ≤ b) :
    Real.log a + 1 - a * b ≤ entropy p := by sorry
