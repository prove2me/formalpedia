-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.neighborSet_nonempty_of_isCubic
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:07:24.211906+00:00
-- url     : https://prove2.me/submissions/10b3a4b5-bbd9-4e93-8fd6-52accdf75cea

-- Sol generated from Bridges/InfiniteCubicMatchingsEquivalence.lean
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










open Bridges.InfiniteCubicMatchings in
theorem solution(hc : IsCubic G) (v : V) :
    (G.neighborSet v).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro h
  have h3 := hc v
  rw [h, Set.ncard_empty] at h3
  exact absurd h3 (by norm_num)
