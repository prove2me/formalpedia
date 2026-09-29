-- Prove2me | solution 1 for AlmostLossless.setMass_mono
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T10:44:16.785163+00:00
-- url     : https://prove2.me/submissions/8cd208dd-98f9-41c9-af0a-ea31deb9dcb5

import Definitions.Def_Bridges_MinEntropy
import Definitions.Def_Bridges_AlmostLosslessCompression
open AlmostLossless NonArchInfoTheory in
theorem solution {α : Type*} [Fintype α] (μ : FinProbDist α) {S T : Finset α} (h : S ⊆ T) :
    setMass μ S ≤ setMass μ T := by
  unfold setMass
  exact Finset.sum_le_sum_of_subset_of_nonneg h (fun x _ _ => μ.mass_nonneg x)
