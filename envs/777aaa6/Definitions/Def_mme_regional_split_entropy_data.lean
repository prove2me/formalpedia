-- Prove2me | Definitions.Def_mme_regional_split_entropy_data
-- name    : mme_regional_split_entropy_data
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-13T20:44:37.270863+00:00
-- url     : https://prove2.me/theorems/38a50212-2b7f-40b9-904b-9332e5857f15
-- title:
--   The summed physical entropy rates of a recursive region
-- statement:
--   Define integer mode marginals and the summed joint, coarse, maximum-entropy penalty, joint parent-mixture and compatibility potentials. The regional rate is the minimum of the three complete regional sums. No cardinality estimate, typicality probability, or entropy rate is assumed.
-- source:
--   Uniform regional entropy estimates for the actual integer CW construction in the More Asymmetry matrix multiplication campaign, https://arxiv.org/html/2404.16349v2#S6 . Supporting result; the numerical surplus certificate remains separate.

import Definitions.Def_mme_regional_entropy_rate_data
import Definitions.Def_mme_recursive_region_parent_profiles
import Definitions.Def_mme_recursive_yz_hash_filter
import Definitions.Def_mme_region_count_entropy_data
open BigOperators
open scoped Classical
set_option autoImplicit false
namespace MME.RegionRate

noncomputable def marginalCounts {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (i : Fin 3) (r : Fin R) (j : Fin (half + 1)) : ℕ :=
  ∑ c : {c : RecursiveThinSplit.Split half (parent r) // c.val i = j}, m r c.val

noncomputable def jointPotential {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ) : ℝ :=
  ∑ r, massEntropy (fun c ↦ (m r c : ℝ))

noncomputable def coarsePotential {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ) (i : Fin 3) : ℝ :=
  ∑ r, massEntropy (fun j ↦ (marginalCounts m i r j : ℝ))

noncomputable def penaltyPotential {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ) : ℝ :=
  ∑ r, (n r : ℝ) * Real.log 2 *
    RecursiveThinSplit.entropyPenalty (fun c ↦ (m r c : ℝ) / n r)

noncomputable def parentPotential {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : RecursiveYZ.Cell half R parent → W → ℕ) : ℝ :=
  ∑ r, (n r : ℝ) * entropy (RegionRealization.parentMixture htotal n m mu r)

noncomputable def compatibilityPotential {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ} (i : Fin 2)
    (mu : RecursiveYZ.Cell half R parent → W → ℕ) : ℝ :=
  RegionRealization.potential (RecursiveYZ.partCount (RecursiveYZ.yzBoundary i)
    (RecursiveYZ.modeGroup (RecursiveYZ.yzMode i)) mu)

/-- The minimum is taken after summing each of the three rates over the whole region. -/
noncomputable def regionalRate {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Fin 3 → RecursiveYZ.Cell half R parent → W → ℕ) : ℝ :=
  min (coarsePotential m 0 - penaltyPotential n m)
    (min (parentPotential htotal n m (mu 1) - compatibilityPotential 0 (mu 1))
      (parentPotential htotal n m (mu 2) - compatibilityPotential 1 (mu 2)))
end MME.RegionRate


