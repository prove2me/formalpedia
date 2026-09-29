-- Prove2me | Theorems.Thm_mme_regional_compatibility_component_sum
-- name    : mme_regional_compatibility_component_sum
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T12:16:51.539371+00:00
-- url     : https://prove2.me/theorems/e225aa96-c2e4-4ba6-8a85-ce569c898f23
-- title:
--   Regional compatibility entropy separates by parent component
-- statement:
--   The actual compatibility potential is exactly the sum of boundary-cell and pooled interior entropies in each parent component. Retained coarse modes and parent labels are preserved; no minimum is moved inside a sum. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_partition_mass_entropy_full_sum
import Definitions.Def_mme_regional_split_entropy_data
open scoped BigOperators Classical
open MME.RegionRate MME.RegionRealization MME.RecursiveYZ

theorem mme_regional_compatibility_component_sum
    {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ} (i : Fin 2)
    (mu : Cell half R parent → W → ℕ) :
    compatibilityPotential i mu = ∑ r : Fin R,
      ((∑ c : MME.RecursiveThinSplit.Split half (parent r),
          if yzBoundary i ⟨r, c⟩ then massEntropy (fun w ↦ (mu ⟨r, c⟩ w : ℝ)) else 0) +
       ∑ a : Fin (half + 1), massEntropy (fun w ↦
         ∑ c : MME.RecursiveThinSplit.Split half (parent r),
           if ¬ yzBoundary i ⟨r, c⟩ ∧ c.val (yzMode i) = a
           then (mu ⟨r, c⟩ w : ℝ) else 0)) := by sorry
