-- Prove2me | solution 1 for KnownUnresolvedCards.E_sum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T01:12:04.215987+00:00
-- url     : https://prove2.me/submissions/7adddde7-681c-42a9-bbc2-cdd7439bebfe

import Definitions.Def_MachineLearning_KnownUnresolvedCards_Basic
open KnownUnresolvedCards in
theorem solution {Ω : Type*} [Fintype Ω] {ι : Type*} (s : Finset ι) (f : ι → Ω → ℚ) :
    E (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, E (f i) := by
  unfold E
  rw [Finset.sum_comm, Finset.sum_div]
