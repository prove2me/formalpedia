-- Prove2me | solution 1 for Catalog.Combinatorics.EvictionOnlineLowerBound.cache_after_miss
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T23:53:38.438626+00:00
-- url     : https://prove2.me/submissions/1dad0ba7-8e07-4aab-8bf7-636a0d043328

import Mathlib
import Definitions.Def_Combinatorics_EvictionOnlineLowerBound
open Finset Catalog.Combinatorics.EvictionOnlineLowerBound in
theorem solution {α : Type*} [DecidableEq α] [Fintype α] {B : ℕ} (hcard : Fintype.card α = B + 1)
    {C : Finset α}
    (hC : C.card = B) {r e : α} (hr : r ∉ C) (he : e ∈ C) :
    insert r (C.erase e) = Finset.univ.erase e := by
  -- a full cache missing `r` is everything except `r`
  have hsub : C ⊆ Finset.univ.erase r :=
    fun x hx => mem_erase.2 ⟨fun h => hr (h ▸ hx), mem_univ x⟩
  have hCeq : C = Finset.univ.erase r := by
    refine eq_of_subset_of_card_le hsub ?_
    rw [card_erase_of_mem (mem_univ r), card_univ, hcard, hC]
    omega
  have hre : r ≠ e := fun h => hr (h ▸ he)
  ext x
  simp only [mem_insert, mem_erase, hCeq, mem_univ, and_true]
  constructor
  · rintro (rfl | ⟨hxe, _⟩)
    · exact hre
    · exact hxe
  · intro hxe
    by_cases hxr : x = r
    · exact Or.inl hxr
    · exact Or.inr ⟨hxe, hxr⟩
