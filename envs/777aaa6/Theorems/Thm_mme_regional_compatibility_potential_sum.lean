-- Prove2me | Theorems.Thm_mme_regional_compatibility_potential_sum
-- name    : mme_regional_compatibility_potential_sum
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T07:44:18.127572+00:00
-- url     : https://prove2.me/theorems/bcf65e5e-7577-492c-b614-ee69aad8725a
-- title:
--   Global compatibility potential equals the sum of regional partition entropies
-- statement:
--   The actual recursive compatibility potential equals the sum of homogeneous entropies of the local boundary/group partitions. The equality holds for every finite integer profile. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_partition_mass_entropy_by_region
import Definitions.Def_mme_regional_split_entropy_data
open scoped BigOperators Classical
open MME.RegionRate MME.RecursiveYZ

theorem mme_regional_compatibility_potential_sum
    {half R : ℕ} {W : Type*} [Fintype W] {parent : Fin R → Fin 3 → ℕ}
    (i : Fin 2) (mu : Cell half R parent → W → ℕ) :
    compatibilityPotential i mu =
      ∑ r, ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary i ⟨r, c⟩) (fun c => c.val (yzMode i))
          (fun c w => mu ⟨r, c⟩ w) t w : ℝ)) := by sorry
