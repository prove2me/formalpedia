-- Prove2me | Definitions.Def_Bridges_InfiniteCubicMatchingsCovers
-- name    : Bridges_InfiniteCubicMatchingsCovers
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:26:06.538047+00:00
-- url     : https://prove2.me/theorems/51a015c1-5516-414c-b0f9-f9e351756b05
-- title:
--   Aether Catalog definitions — Bridges_InfiniteCubicMatchingsCovers
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.InfiniteCubicMatchingsCovers`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/InfiniteCubicMatchingsCovers.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsCompactness
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

namespace Bridges.InfiniteCubicMatchings

universe u v

variable {V : Type u} {W : Type v} {G : SimpleGraph V} {K : SimpleGraph W}

namespace PerfectMatching

/-- The partner map obtained by pulling a perfect matching of `K` back along a covering. -/
noncomputable def pullbackPartner (φ : V → W) (hcov : ∀ v, IsLocalIsoAt G K φ v)
    (M : PerfectMatching K) (v : V) : V :=
  Classical.choose ((hcov v).surj (M.partner (φ v)) (M.isAdj (φ v)))

lemma pullbackPartner_adj (φ : V → W) (hcov : ∀ v, IsLocalIsoAt G K φ v)
    (M : PerfectMatching K) (v : V) : G.Adj v (pullbackPartner φ hcov M v) :=
  (Classical.choose_spec ((hcov v).surj (M.partner (φ v)) (M.isAdj (φ v)))).1

lemma pullbackPartner_map (φ : V → W) (hcov : ∀ v, IsLocalIsoAt G K φ v)
    (M : PerfectMatching K) (v : V) :
    φ (pullbackPartner φ hcov M v) = M.partner (φ v) :=
  (Classical.choose_spec ((hcov v).surj (M.partner (φ v)) (M.isAdj (φ v)))).2

/-- Pulling back a perfect matching along a covering map. -/
noncomputable def pullback (φ : V → W) (hcov : ∀ v, IsLocalIsoAt G K φ v)
    (M : PerfectMatching K) : PerfectMatching G where
  partner := pullbackPartner φ hcov M
  isAdj := pullbackPartner_adj φ hcov M
  invol v := by
    set y := pullbackPartner φ hcov M v with hy
    have hvy : G.Adj v y := pullbackPartner_adj φ hcov M v
    have h1 : φ (pullbackPartner φ hcov M y) = φ v := by
      rw [pullbackPartner_map φ hcov M y, hy, pullbackPartner_map φ hcov M v, M.invol]
    exact (hcov y).inj _ _ (pullbackPartner_adj φ hcov M y) hvy.symm h1


end PerfectMatching





end Bridges.InfiniteCubicMatchings


