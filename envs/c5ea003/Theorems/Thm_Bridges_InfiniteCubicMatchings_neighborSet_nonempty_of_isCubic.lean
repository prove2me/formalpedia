-- Prove2me | Theorems.Thm_Bridges_InfiniteCubicMatchings_neighborSet_nonempty_of_isCubic
-- name    : Bridges.InfiniteCubicMatchings.neighborSet_nonempty_of_isCubic
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:29:05.648789+00:00
-- url     : https://prove2.me/theorems/69ae2ba1-3d84-453d-b2ca-128a0d0d4eb9
-- title:
--   In a cubic graph no vertex is isolated.
-- statement:
--   In a cubic graph no vertex is isolated.
--
--   ```lean
--   theorem Bridges.InfiniteCubicMatchings.neighborSet_nonempty_of_isCubic(hc : IsCubic G) (v : V) :
--       (G.neighborSet v).Nonempty := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/InfiniteCubicMatchingsEquivalence.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/InfiniteCubicMatchingsEquivalence.lean#L58

-- Thm stub generated from Bridges/InfiniteCubicMatchingsEquivalence.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
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

theorem Bridges.InfiniteCubicMatchings.neighborSet_nonempty_of_isCubic(hc : IsCubic G) (v : V) :
    (G.neighborSet v).Nonempty := by sorry
