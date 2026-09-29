-- Prove2me | solution 1 for mme_regional_compatibility_potential_sum
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T07:45:53.188239+00:00
-- url     : https://prove2.me/submissions/ecc5c62f-c644-4bc3-9a04-e477fd7bb464

import Theorems.Thm_mme_partition_mass_entropy_by_region
import Definitions.Def_mme_regional_split_entropy_data

open scoped BigOperators Classical
open MME.RegionRate MME.RecursiveYZ

/-- Compatibility potential splits into the homogeneous entropies of the
local partitions because each merged group retains its region label. -/
theorem solution
    {half R : ℕ} {W : Type*} [Fintype W] {parent : Fin R → Fin 3 → ℕ}
    (i : Fin 2) (mu : Cell half R parent → W → ℕ) :
    compatibilityPotential i mu =
      ∑ r, ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary i ⟨r, c⟩) (fun c => c.val (yzMode i))
          (fun c w => mu ⟨r, c⟩ w) t w : ℝ)) := by
  rw [compatibilityPotential, (mme_regional_mass_entropy_algebra).2.2]
  simpa only [modeGroup] using mme_partition_mass_entropy_by_region (yzBoundary i)
    (fun r c => c.val (yzMode i)) mu


#print axioms solution
