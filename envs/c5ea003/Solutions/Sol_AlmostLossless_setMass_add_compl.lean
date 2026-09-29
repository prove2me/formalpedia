-- Prove2me | solution 1 for AlmostLossless.setMass_add_compl
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T10:55:08.16546+00:00
-- url     : https://prove2.me/submissions/faf10615-114a-4b03-98b9-51b5c4494ae1

import Definitions.Def_Bridges_MinEntropy
import Definitions.Def_Bridges_AlmostLosslessCompression
open AlmostLossless NonArchInfoTheory in
theorem solution {α : Type*} [Fintype α] (μ : FinProbDist α) [DecidableEq α] (S : Finset α) :
    setMass μ S + setMass μ Sᶜ = 1 := by
  unfold setMass
  rw [Finset.sum_add_sum_compl]
  exact μ.mass_sum_one
