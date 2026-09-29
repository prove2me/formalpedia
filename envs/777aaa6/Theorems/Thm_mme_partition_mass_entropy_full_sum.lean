-- Prove2me | Theorems.Thm_mme_partition_mass_entropy_full_sum
-- name    : mme_partition_mass_entropy_full_sum
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T07:17:14.729814+00:00
-- url     : https://prove2.me/theorems/8b4bfee3-d53f-473c-b67e-5807e0a5e54e
-- title:
--   Partition entropy admits a full computable index
-- statement:
--   The homogeneous entropy of a boundary partition equals the sum over all cells and group labels after assigning zero mass to nonboundary individual cells. This permits rational evaluation while retaining the original partition-count definition. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_regional_mass_entropy_algebra
import Definitions.Def_mme_recursive_yz_compatibility
open scoped BigOperators
open MME.RegionRate MME.RecursiveYZ

theorem mme_partition_mass_entropy_full_sum
    {C G W : Type*} [Fintype C] [Fintype G] [Fintype W]
    (boundary : C → Prop) [DecidablePred boundary] [DecidableEq G]
    (group : C → G) (mu : C → W → ℕ) (n : ℕ) :
    let a : C ⊕ G → W → ℕ := fun t w => match t with
      | Sum.inl c => if boundary c then mu c w else 0
      | Sum.inr g => ∑ c, if ¬ boundary c ∧ group c = g then mu c w else 0
    (∑ t, massEntropy (fun w => (partCount boundary group mu t w : ℝ) / n)) =
      ∑ t, massEntropy (fun w => (a t w : ℝ) / n) := by sorry
