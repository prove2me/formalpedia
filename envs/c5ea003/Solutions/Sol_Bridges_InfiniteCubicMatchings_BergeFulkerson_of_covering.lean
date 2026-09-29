-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.BergeFulkerson.of_covering
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T13:45:30.736977+00:00
-- url     : https://prove2.me/submissions/ec02b542-d860-49e2-99bf-1f03e56e68ff

-- Sol generated from Bridges/InfiniteCubicMatchingsCovers.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsCompactness
import Definitions.Def_Bridges_InfiniteCubicMatchingsCovers
import Theorems.Thm_Bridges_InfiniteCubicMatchings_PerfectMatching_mem_edges
/-
# Coverings: transferring matchings from a base graph to an infinite cover

A map `φ : V(G) → V(K)` which is a local isomorphism at *every* vertex (`IsLocalIsoAt`) is a
covering map in the graph-theoretic sense.  Perfect matchings pull back along such maps, and
therefore so do the Berge–Fulkerson and Fan–Raspaud properties.

The consequence for the infinite theory is `bergeFulkerson_of_covers_finite`: *the finite
Berge–Fulkerson conjecture already implies the Berge–Fulkerson property for every graph —
however large — that covers a finite cubic bridgeless graph.*  This covers all the standard
infinite examples (ℤ-covers and other regular covers of finite snarks and prisms), with no
compactness argument needed.
-/

open Bridges.InfiniteCubicMatchings

universe u v

variable {V : Type u} {W : Type v} {G : SimpleGraph V} {K : SimpleGraph W}

open PerfectMatching





/-- An edge belongs to the pulled back matching exactly when its image belongs to the original
one. -/
lemma mem_pullback_edges (φ : V → W) (hcov : ∀ v, IsLocalIsoAt G K φ v)
    (M : PerfectMatching K) (u w : V) (huw : G.Adj u w) :
    s(u, w) ∈ (pullback φ hcov M).edges ↔ s(φ u, φ w) ∈ M.edges := by
  rw [mem_edges, mem_edges]
  constructor
  · intro h
    rw [← pullbackPartner_map φ hcov M u]
    exact congrArg φ (by rw [← h]; rfl)
  · intro h
    refine (hcov u).inj _ _ (pullbackPartner_adj φ hcov M u) huw ?_
    show φ (pullbackPartner φ hcov M u) = φ w
    rw [pullbackPartner_map φ hcov M u, h]







open Bridges.InfiniteCubicMatchings in
theorem solution(φ : V → W) (hcov : ∀ v, IsLocalIsoAt G K φ v)
    (hK : BergeFulkerson K) : BergeFulkerson G := by
  obtain ⟨M, hM⟩ := hK
  refine ⟨fun i => PerfectMatching.pullback φ hcov (M i), ?_⟩
  intro e
  induction e with
  | _ u w =>
    intro hE
    have huw : G.Adj u w := hE
    have hset : {i : Fin 6 | s(u, w) ∈ (PerfectMatching.pullback φ hcov (M i)).edges}
        = {i : Fin 6 | s(φ u, φ w) ∈ (M i).edges} := by
      ext i
      exact mem_pullback_edges φ hcov (M i) u w huw
    rw [hset]
    exact hM _ (by simpa using (hcov u).adj w huw)
