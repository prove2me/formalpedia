-- Prove2me | solution 1 for ErdosFaberLovasz.erase_disjoint_of_common_vertex
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T14:28:17.383751+00:00
-- url     : https://prove2.me/submissions/6f6e3c29-6bd3-4400-9398-af6ee9066486

-- Sol generated from Combinatorics/ErdosFaberLovasz.lean
import Mathlib
import Definitions.Def_Combinatorics_ErdosFaberLovasz

open Finset

open ErdosFaberLovasz

variable {V : Type*} [DecidableEq V]















open ErdosFaberLovasz in
theorem solution{H : Hypergraph V} (hlin : IsLinear H)
    {e f : Finset V} (he : e ∈ H) (hf : f ∈ H) (hne : e ≠ f)
    {x : V} (hxe : x ∈ e) (hxf : x ∈ f) :
    Disjoint (e.erase x) (f.erase x) := by
  rw [Finset.disjoint_left]
  intro y hye hyf
  rw [Finset.mem_erase] at hye hyf
  obtain ⟨hyne, hye⟩ := hye
  obtain ⟨_, hyf⟩ := hyf
  have hcard : (e ∩ f).card ≤ 1 := hlin e he f hf hne
  have hxfy : x ∈ e ∩ f := Finset.mem_inter.mpr ⟨hxe, hxf⟩
  have hyxf : y ∈ e ∩ f := Finset.mem_inter.mpr ⟨hye, hyf⟩
  have hcard2 : (e ∩ f).card ≥ 2 := by
    have hsub : {x, y} ⊆ e ∩ f := by
      rw [Finset.insert_subset_iff]
      exact ⟨hxfy, Finset.singleton_subset_iff.mpr hyxf⟩
    calc (e ∩ f).card ≥ (({x, y} : Finset V)).card := Finset.card_le_card hsub
      _ = 2 := Finset.card_pair hyne.symm
  linarith
