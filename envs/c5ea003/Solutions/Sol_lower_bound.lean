-- Prove2me | solution 1 for lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T22:57:26.988961+00:00
-- url     : https://prove2.me/submissions/8536093a-c98c-4a1c-bcd3-90cde8198eeb

import Mathlib
import Definitions.Def_Novelty_TransmissionDominationTree
theorem solution (n : ℕ) (S : Finset ℕ) (h : DominatesPath n S) : n ≤ 3 * S.card := by
  obtain ⟨-, hdom⟩ := h
  -- every path vertex lies in the closed neighbourhood `{s-1, s, s+1}` of some guard
  have hsub : Finset.range n ⊆ S.biUnion blockP := by
    intro i hi
    obtain ⟨s, hs, h1, h2⟩ := hdom i hi
    rw [Finset.mem_biUnion]
    exact ⟨s, hs, by rw [blockP, Finset.mem_Icc]; omega⟩
  -- and each neighbourhood has at most three vertices
  have hblock : ∀ s, (blockP s).card ≤ 3 := by
    intro s
    rw [blockP, Nat.card_Icc]
    omega
  calc n = (Finset.range n).card := (Finset.card_range n).symm
    _ ≤ (S.biUnion blockP).card := Finset.card_le_card hsub
    _ ≤ ∑ s ∈ S, (blockP s).card := Finset.card_biUnion_le
    _ ≤ ∑ _s ∈ S, 3 := Finset.sum_le_sum fun s _ => hblock s
    _ = 3 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
