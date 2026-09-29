-- Prove2me | Definitions.Def_Bridges_InfiniteCubicMatchingsEquivalence
-- name    : Bridges_InfiniteCubicMatchingsEquivalence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:27:36.639222+00:00
-- url     : https://prove2.me/theorems/5801afa3-cbef-4aef-97b3-193280f5e4af
-- title:
--   Aether Catalog definitions — Bridges_InfiniteCubicMatchingsEquivalence
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.InfiniteCubicMatchingsEquivalence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/InfiniteCubicMatchingsEquivalence.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsCompactness
import Definitions.Def_Bridges_InfiniteCubicMatchingsCovers
/-
# The finite and the infinite Berge–Fulkerson conjectures are equivalent

The paper's headline claim is that the *finite* versions of the Berge–Fulkerson, Fan–Raspaud
and Máčajová–Škoviera conjectures are equivalent to their *infinite* versions.  One direction
is trivial (a finite graph is a graph); the substance is the converse, which is a compactness
argument fed by *finite local models*.

This file isolates the class of graphs for which the argument goes through,

  `HasFiniteLocalModels G` : around every finite set of vertices, `G` looks locally exactly
  like some finite cubic bridgeless graph,

and proves the equivalence

  `finiteBergeFulkerson_iff` :
      FiniteBergeFulkersonConjecture
        ↔ every locally finite graph without isolated vertices that has finite local models
          satisfies Berge–Fulkerson.

The forward implication is the compactness transfer `bergeFulkerson_of_finite_local_models`;
the backward implication uses `hasFiniteLocalModels_self`, i.e. a finite cubic bridgeless
graph is its own local model.  The class is genuinely larger than the finite graphs:
`hasFiniteLocalModels_of_covering` shows that every covering of a finite cubic bridgeless
graph — for instance the infinite ℤ-voltage lifts of `InfiniteCubicMatchingsPetersenLift` and
the Cayley graphs of `InfiniteCubicMatchingsCayley` — belongs to it.
-/

namespace Bridges.InfiniteCubicMatchings

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- `G` *has finite local models* if around every finite set of vertices it is locally
isomorphic to a finite cubic bridgeless graph. -/
def HasFiniteLocalModels (G : SimpleGraph V) : Prop :=
  ∀ T : Finset V, ∃ (W : Type) (_ : Fintype W) (K : SimpleGraph W) (φ : V → W),
    IsCubic K ∧ Bridgeless K ∧ ∀ v ∈ T, IsLocalIsoAt G K φ v








end Bridges.InfiniteCubicMatchings


