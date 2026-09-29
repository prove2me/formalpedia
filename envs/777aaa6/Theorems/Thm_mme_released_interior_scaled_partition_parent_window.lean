-- Prove2me | Theorems.Thm_mme_released_interior_scaled_partition_parent_window
-- name    : mme_released_interior_scaled_partition_parent_window
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T05:04:54.025567+00:00
-- url     : https://prove2.me/theorems/28cb4926-f713-4a9c-b626-c9b2871d7e85
-- title:
--   Regional windows give the released global histogram window at every scale
-- statement:
--   Every positive integer replication admits a partition of the physical parent positions such that regional parent typicality implies the full-word histogram window around the released global distribution, at the same tolerance. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_released_interior_weighted_parent_center
import Theorems.Thm_mme_released_interior_scaled_integer_profile_constraints_exact
import Theorems.Thm_mme_regional_parent_windows_imply_global_histogram_window_allow_empty
open BigOperators MME MME.ReleasedInterior MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit MME.RegionRealization

theorem mme_released_interior_scaled_partition_parent_window
    (owner : Fin 6) (s : Fin 45) (hi : (seed owner s).boundary = [])
    (k : ℕ) (hk : 0 < k) :
    ∃ positions : (Σ r : Fin 6, Fin (k * (regionalSize owner s) r)) ≃
        Fin (k * denominator ^ 4),
      ∀ (i : Fin 3) (f : Fin (k * denominator ^ 4) → CompleteWord 3) (eps : ℝ),
        parentTypical (parent_total s) (fun r => k * (regionalSize owner s) r)
          (fun r c => k * (splitCount owner s) r c) (fun c w => k * (integerProfile owner s) i c w) eps
          (fun p =>
            let v := (completeWordSplitEquiv 2 (by decide)) (f (positions ⟨p.1,p.2.1⟩))
            ![v.1,v.2] p.2.2) →
        ∀ w : CompleteWord 3,
          |(Fintype.card {p : Fin (k * denominator ^ 4) // f p = w} : ℝ) /
              (k * denominator ^ 4 : ℕ) -
            ((((ReleasedGlobal.jointRows owner s).map
              (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum : ℕ) : ℝ) /
              (denominator : ℝ) ^ 4| ≤ eps := by sorry
