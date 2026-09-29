-- Prove2me | solution 1 for AlmostLossless.setMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T07:02:57.598285+00:00
-- url     : https://prove2.me/submissions/63ee2ed4-e476-4d02-ae00-6b6978ddc4db

import Definitions.Def_Bridges_MinEntropy
import Definitions.Def_Bridges_AlmostLosslessCompression

open AlmostLossless NonArchInfoTheory

open AlmostLossless NonArchInfoTheory in
/-- **The mass of any set is nonnegative.** -/
theorem solution {α : Type*} [Fintype α] (μ : NonArchInfoTheory.FinProbDist α) (S : Finset α) :
    0 ≤ AlmostLossless.setMass μ S := by
  unfold AlmostLossless.setMass
  exact Finset.sum_nonneg (fun x _ => μ.mass_nonneg x)
