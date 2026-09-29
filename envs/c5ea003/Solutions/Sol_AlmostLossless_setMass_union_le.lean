-- Prove2me | solution 1 for AlmostLossless.setMass_union_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T10:49:27.836009+00:00
-- url     : https://prove2.me/submissions/33e3279a-e68b-41c5-84a6-459bdaa5524d

import Definitions.Def_Bridges_MinEntropy
import Definitions.Def_Bridges_AlmostLosslessCompression
open AlmostLossless NonArchInfoTheory in
theorem solution {α : Type*} [Fintype α] (μ : FinProbDist α) [DecidableEq α] (S T : Finset α) :
    setMass μ (S ∪ T) ≤ setMass μ S + setMass μ T := by
  unfold setMass
  have h := Finset.sum_union_inter (s₁ := S) (s₂ := T) (f := μ.mass)
  have h0 : 0 ≤ ∑ x ∈ S ∩ T, μ.mass x := Finset.sum_nonneg (fun x _ => μ.mass_nonneg x)
  linarith
