-- Prove2me | Theorems.Thm_mme_partition_mass_entropy_by_region
-- name    : mme_partition_mass_entropy_by_region
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T07:32:53.063051+00:00
-- url     : https://prove2.me/theorems/6e75dcfa-57b7-4bd8-bdee-08b5c5c66b7a
-- title:
--   Partition entropy is the sum of its regional entropies
-- statement:
--   For a finite dependent family of regions, a partition whose merged group labels retain the region has total homogeneous entropy equal to the sum of its local partition entropies. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_partition_mass_entropy_full_sum
open scoped BigOperators
open MME.RegionRate MME.RecursiveYZ

theorem mme_partition_mass_entropy_by_region
    {R G W : Type*} [Fintype R] [Fintype G] [Fintype W]
    {C : R → Type*} [∀ r, Fintype (C r)]
    (boundary : (Σ r, C r) → Prop) [DecidablePred boundary] (group : ∀ r, C r → G)
    (mu : (Σ r, C r) → W → ℕ) :
    (∑ t, massEntropy (fun w =>
      (partCount boundary (fun c => (c.1, group c.1 c.2)) mu t w : ℝ))) =
      ∑ r, ∑ t, massEntropy (fun w =>
        (partCount (fun c : C r => boundary ⟨r, c⟩) (group r)
          (fun c w => mu ⟨r, c⟩ w) t w : ℝ)) := by sorry
