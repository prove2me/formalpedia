-- Prove2me | solution 1 for mme_released_interior_zero_region_volume
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:41:52.909981+00:00
-- url     : https://prove2.me/submissions/47918864-267d-48a5-8e1c-4f34c899391a

import Definitions.Def_mme_released_interior_integer_profiles
import Theorems.Thm_mme_boundary_profile_volume_mass_entropy

open scoped BigOperators
open MME MME.ReleasedInterior MME.MoreAsymmetryExactSeed MME.RecursiveYZ
open MME.RegionRate MME.RegionRealization MME.CompleteSplit
open MME.RecursiveYZ.Boundary

/-- A zero-mass region contributes zero entropy and letter volume for every
actual child and every choice of free mode. -/
theorem solution
    (owner : Fin 6) (s : Fin 45) (c : Cell 4 6 (parent s))
    (hzero : (seed owner s).region.getD c.1.val 0 = 0) (i : Fin 3) :
    massEntropy (fun w ↦ (integerProfile owner s i c w : ℝ)) +
      ((∑ w, integerProfile owner s i c w * ones w : ℕ) : ℝ) *
        Real.log 5 = 0 := by
  have hprofile (w : CompleteWord 2) : integerProfile owner s i c w = 0 := by
    unfold integerProfile
    rw [hzero]
    simp
  simp only [hprofile, Nat.cast_zero, zero_mul, Finset.sum_const_zero]
  simp [massEntropy, entropy]


#print axioms solution
