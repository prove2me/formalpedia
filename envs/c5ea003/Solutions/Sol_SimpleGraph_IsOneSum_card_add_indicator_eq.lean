-- Prove2me | solution 1 for SimpleGraph.IsOneSum.card_add_indicator_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T07:49:18.42+00:00
-- url     : https://prove2.me/submissions/8dc192c2-6442-47aa-bbdd-b5efe1d1fdee

import Mathlib
import Definitions.Def_Novelty_IndependenceRatioChromatic
import Definitions.Def_Novelty_OneSumEqualityAnalysis
open Finset SimpleGraph in
theorem solution {V : Type*} {G G₁ G₂ : SimpleGraph V} {A B : Set V} {v : V}
    (h : IsOneSum G G₁ G₂ A B v) [Fintype V] [DecidableEq V] (s : Finset V)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] :
    s.card + (if v ∈ s then 1 else 0)
      = (s.filter (· ∈ A)).card + (s.filter (· ∈ B)).card := by
  -- the two sides cover `s` and overlap exactly in the cut vertex
  have hU : s.filter (· ∈ A) ∪ s.filter (· ∈ B) = s := by
    ext x
    simp only [mem_union, mem_filter]
    constructor
    · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
    · intro hx
      have hxu : x ∈ A ∪ B := by rw [h.union_eq]; exact Set.mem_univ x
      rcases hxu with hA | hB
      · exact Or.inl ⟨hx, hA⟩
      · exact Or.inr ⟨hx, hB⟩
  have hI : s.filter (· ∈ A) ∩ s.filter (· ∈ B) = s.filter (fun x => x = v) := by
    ext x
    simp only [mem_inter, mem_filter]
    constructor
    · rintro ⟨⟨hx, hA⟩, -, hB⟩
      have : x ∈ A ∩ B := ⟨hA, hB⟩
      rw [h.inter_eq] at this
      exact ⟨hx, this⟩
    · rintro ⟨hx, rfl⟩
      have : x ∈ A ∩ B := by rw [h.inter_eq]; exact Set.mem_singleton x
      exact ⟨⟨hx, this.1⟩, hx, this.2⟩
  have hv : (s.filter (fun x => x = v)).card = if v ∈ s then 1 else 0 := by
    rw [filter_eq']
    split_ifs <;> simp
  rw [← card_union_add_card_inter, hU, hI, hv]
