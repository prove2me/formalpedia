-- Prove2me | solution 1 for AlmostLossless.setMass_le_card_mul_maxMass
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T12:24:21.918274+00:00
-- url     : https://prove2.me/submissions/ffa5e56c-844a-4be7-8501-266953050889

import Definitions.Def_Bridges_AlmostLosslessCompression
import Definitions.Def_Bridges_MinEntropy
open AlmostLossless NonArchInfoTheory in
theorem solution {α : Type*} [Fintype α] [Nonempty α] (μ : FinProbDist α) (S : Finset α) :
    setMass μ S ≤ (S.card : ℝ) * maxMass μ := by
  unfold setMass
  calc ∑ x ∈ S, μ.mass x ≤ ∑ _x ∈ S, maxMass μ :=
        Finset.sum_le_sum (fun x _ => Finset.le_sup' μ.mass (Finset.mem_univ x))
    _ = (S.card : ℝ) * maxMass μ := by simp
