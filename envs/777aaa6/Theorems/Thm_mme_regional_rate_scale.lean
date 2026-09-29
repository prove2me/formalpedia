-- Prove2me | Theorems.Thm_mme_regional_rate_scale
-- name    : mme_regional_rate_scale
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T23:36:09.664449+00:00
-- url     : https://prove2.me/theorems/a5ca951a-2427-467b-90a2-9ddc2e9acf3f
-- title:
--   Regional extraction rate under uniform replication
-- statement:
--   For a positive integer replication factor k, replicating parent sizes, split counts, and all child profile counts multiplies the regional extraction rate by k. The minimum is taken after summing each mode rate across all regions.
-- source:
--   Entropy scaling for the released regional extraction: homogeneous mass entropy, invariant normalized parent mixtures, and fixed-tolerance losses.

import Definitions.Def_mme_regional_entropy_copy_bound
import Theorems.Thm_mme_regional_mass_entropy_algebra
import Mathlib.Tactic.Ring
import Definitions.Def_mme_recursive_region_parent_profiles
import Mathlib.Algebra.Order.Field.Basic
open scoped Classical
open BigOperators MME MME.RecursiveYZ MME.RegionRealization
open MME.RegionRate
set_option autoImplicit false
universe u

theorem mme_regional_rate_scale {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Fin 3 → Cell half R parent → W → ℕ) (k : ℕ) (hk : 0 < k) :
    regionalRate htotal (fun r => k * n r) (fun r c => k * m r c)
      (fun i c w => k * mu i c w) = (k : ℝ) * regionalRate htotal n m mu := by sorry
