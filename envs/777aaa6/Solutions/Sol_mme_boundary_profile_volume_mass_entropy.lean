-- Prove2me | solution 1 for mme_boundary_profile_volume_mass_entropy
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:09:45.657103+00:00
-- url     : https://prove2.me/submissions/a6ed5452-ec0f-4f99-b639-adaa9e13b28b

import Theorems.Thm_mme_regional_mass_entropy_algebra
import Definitions.Def_mme_recursive_yz_boundary_data

open scoped BigOperators
open MME MME.RegionRate MME.RegionRealization MME.CompleteSplit MME.RecursiveYZ.Boundary

/-- A boundary profile's entropy and letter-volume rate is determined by the
actual counts in the cyclically next, free mode. Empty profiles are included. -/
theorem solution {ell L : ℕ}
    (B : Profile ell L) (z : Fin 3) (mu : Fin 3 → CompleteWord ell → ℕ)
    (hmu : ∀ i w, mu i w = B.mu z i w) :
    (L : ℝ) * Real.log 2 *
        mme_modern_entropyBits (fun w ↦ (B.count w : ℝ) / (L : ℝ)) +
      ((∑ w, B.count w * ones w : ℕ) : ℝ) * Real.log 5 =
    massEntropy (fun w ↦ (mu (z + 1) w : ℝ)) +
      ((∑ w, mu (z + 1) w * ones w : ℕ) : ℝ) * Real.log 5 := by
  have hb (w : CompleteWord ell) : mu (z + 1) w = B.count w := by
    fin_cases z
    · simpa [Profile.mu] using hmu 1 w
    · simpa [Profile.mu] using hmu 2 w
    · simpa [Profile.mu] using hmu 0 w
  have he : (L : ℝ) * Real.log 2 *
      mme_modern_entropyBits (fun w ↦ (B.count w : ℝ) / (L : ℝ)) =
      massEntropy (fun w ↦ (B.count w : ℝ)) := by
    simpa [potential, B.total] using
      (mme_regional_mass_entropy_algebra (C := Unit) (W := CompleteWord ell)).2.2
        (fun _ w ↦ B.count w)
  simp_rw [hb]
  rw [he]


#print axioms solution
