-- Prove2me | Theorems.Thm_mme_regional_physical_parent_type_entropy_bound
-- name    : mme_regional_physical_parent_type_entropy_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T20:47:45.038172+00:00
-- url     : https://prove2.me/theorems/672e1153-25bf-4e4b-93a2-2507aafed86d
-- title:
--   Uniform entropy lower bound for actual physical parent-type denominators
-- statement:
--   Bound the actual ParentType cardinality used in regional hash loads below by the joint parent-mixture entropy minus coarse-mode entropy and the explicit uniform continuity loss. The bound holds for every target address and every graded parent-typical word. The region is summed jointly, with a single explicit polynomial factor.
-- source:
--   Uniform regional entropy estimates for the actual integer CW construction in the More Asymmetry matrix multiplication campaign, https://arxiv.org/html/2404.16349v2#S6 . Supporting result; the numerical surplus certificate remains separate.

import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_regional_split_entropy_data
import Mathlib
open BigOperators MME MME.RegionRate MME.RecursiveYZ MME.CompleteSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem mme_regional_physical_parent_type_entropy_bound {half R ell : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (hmass : ∀ r, ∑ c, m r c = n r) (mu : Cell half R parent → CompleteWord ell → ℕ)
    (i : Fin 3) (eps : ℝ) (heps : 0 ≤ eps)
    (a : Address half R parent n) (ha : a ∈ RecursiveXHash.target m)
    (f : Position n → CompleteWord ell) (hg : Graded htotal i a f)
    (ht : RegionRealization.parentTypical htotal n m mu eps f) :
    Real.exp (parentPotential htotal n m mu - coarsePotential m i -
      ((∑ r, n r : ℕ) : ℝ) * entropyModulus (Fin 2 → CompleteWord ell) eps) ≤
      (6 * (((∑ r, n r : ℕ) : ℝ) + 1)) ^
        (R * (half + 1) * Fintype.card (Fin 2 → CompleteWord ell)) *
        Nat.card {g : Position n → CompleteWord ell //
          ParentType (RecursiveXHash.block i a) (parentCounts (RecursiveXHash.block i a) f) g} := by sorry
