-- Prove2me | Theorems.Thm_Bridges_InfiniteCubicMatchings_isLocalIsoAt_id
-- name    : Bridges.InfiniteCubicMatchings.isLocalIsoAt_id
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:27:25.904561+00:00
-- url     : https://prove2.me/theorems/1ef6e534-0474-466a-80ea-3dc245a51a8e
-- title:
--   The identity is a local isomorphism at every vertex.
-- statement:
--   The identity is a local isomorphism at every vertex.
--
--   ```lean
--   theorem Bridges.InfiniteCubicMatchings.isLocalIsoAt_id(G : SimpleGraph V) (v : V) : IsLocalIsoAt G G id v := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/InfiniteCubicMatchingsEquivalence.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/InfiniteCubicMatchingsEquivalence.lean#L41

-- Thm stub generated from Bridges/InfiniteCubicMatchingsEquivalence.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchingsCompactness
import Definitions.Def_Bridges_InfiniteCubicMatchingsCovers
import Definitions.Def_Bridges_InfiniteCubicMatchingsEquivalence
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

open Bridges.InfiniteCubicMatchings

universe u

variable {V : Type u} {G : SimpleGraph V}

theorem Bridges.InfiniteCubicMatchings.isLocalIsoAt_id(G : SimpleGraph V) (v : V) : IsLocalIsoAt G G id v := by sorry
