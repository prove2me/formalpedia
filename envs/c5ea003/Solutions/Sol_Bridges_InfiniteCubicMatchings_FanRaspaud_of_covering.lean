-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.FanRaspaud.of_covering
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T11:29:36.130805+00:00
-- url     : https://prove2.me/submissions/8ea7d5d5-ed54-405c-8b5e-3e3e2b49dd9d

import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsCompactness
import Definitions.Def_Bridges_InfiniteCubicMatchingsCovers
open Bridges.InfiniteCubicMatchings in
theorem solution {V : Type*} {W : Type*} {G : SimpleGraph V} {K : SimpleGraph W}
    (φ : V → W) (hcov : ∀ v, IsLocalIsoAt G K φ v)
    (hK : FanRaspaud K) : FanRaspaud G := by
  obtain ⟨M, hM⟩ := hK
  refine ⟨fun i => PerfectMatching.pullback φ hcov (M i), ?_⟩
  -- an edge of a pulled-back matching maps to an edge of the original matching
  have hmap : ∀ i e, e ∈ (PerfectMatching.pullback φ hcov (M i)).edges →
      Sym2.map φ e ∈ (M i).edges := by
    rintro i e ⟨v, rfl⟩
    refine ⟨φ v, ?_⟩
    show Sym2.map φ s(v, PerfectMatching.pullbackPartner φ hcov (M i) v) = _
    rw [Sym2.map_mk, PerfectMatching.pullbackPartner_map φ hcov (M i) v]
  ext e
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨h0, h1⟩, h2⟩
  have h : Sym2.map φ e ∈ (M 0).edges ∩ (M 1).edges ∩ (M 2).edges :=
    ⟨⟨hmap 0 e h0, hmap 1 e h1⟩, hmap 2 e h2⟩
  rw [hM] at h
  exact h
