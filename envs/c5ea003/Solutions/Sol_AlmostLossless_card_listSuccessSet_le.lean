-- Prove2me | solution 1 for AlmostLossless.card_listSuccessSet_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T12:01:41.821314+00:00
-- url     : https://prove2.me/submissions/05ae9b59-611d-4498-82db-c6cffc43ad1c

import Definitions.Def_Bridges_AlmostLosslessListDecoding
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
open AlmostLossless in
theorem solution {α : Type*} [Fintype α] [DecidableEq α] {Code : Type*} [Fintype Code]
    [DecidableEq Code] (s : ListScheme α Code) (T : ℕ) (hT : ∀ c, (s.dec c).length ≤ T) :
    (listSuccessSet s).card ≤ Fintype.card Code * T := by
  calc (listSuccessSet s).card
      ≤ (Finset.univ.biUnion fun c => (s.dec c).toFinset).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [listSuccessSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, List.mem_toFinset]
        exact ⟨s.enc x, hx⟩
    _ ≤ ∑ c, (s.dec c).toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _c : Code, T := Finset.sum_le_sum fun c _ => (List.toFinset_card_le _).trans (hT c)
    _ = Fintype.card Code * T := by simp
