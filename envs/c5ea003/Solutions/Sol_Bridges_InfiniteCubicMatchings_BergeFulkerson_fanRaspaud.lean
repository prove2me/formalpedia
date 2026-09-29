-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.BergeFulkerson.fanRaspaud
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T11:15:35.202897+00:00
-- url     : https://prove2.me/submissions/dcb09dc3-e20a-4196-8fe0-c890374804ba

import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
open Bridges.InfiniteCubicMatchings in
theorem solution {V : Type*} {G : SimpleGraph V} (h : BergeFulkerson G) : FanRaspaud G := by
  obtain ⟨M, hM⟩ := h
  refine ⟨![M 0, M 1, M 2], ?_⟩
  ext e
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨h0, h1⟩, h2⟩
  have h0' : e ∈ (M 0).edges := h0
  have h1' : e ∈ (M 1).edges := h1
  have h2' : e ∈ (M 2).edges := h2
  -- `e` is an edge of `G`, lying in exactly two of the six matchings
  obtain ⟨v, rfl⟩ := h0'
  have he : s(v, (M 0).partner v) ∈ G.edgeSet := (M 0).isAdj v
  have hthree : 2 < {i : Fin 6 | s(v, (M 0).partner v) ∈ (M i).edges}.ncard := by
    rw [Set.two_lt_ncard_iff (Set.toFinite _)]
    exact ⟨0, 1, 2, ⟨v, rfl⟩, h1', h2', by decide, by decide, by decide⟩
  rw [hM _ he] at hthree
  exact lt_irrefl 2 hthree
