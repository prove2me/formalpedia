-- Prove2me | Definitions.Def_Novelty_General
-- name    : Novelty_General
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:07:10.029633+00:00
-- url     : https://prove2.me/theorems/7c10a020-60c5-4746-83cd-d9bc43a519c2
-- title:
--   Aether Catalog definitions — Novelty_General
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.General`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/General.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cycle-containing families of vectors: the general alphabet bound

## Setup

Fix an alphabet size `b` and a length `k`.  To each ordered pair of vectors
`u v : Fin k → Fin b` we associate a **bipartite graph** `pairGraph u v` on the
vertex set `Fin b ⊕ Fin b`:  the left copy and the right copy of the alphabet.
For every coordinate `i` we put an edge between `Sum.inl (u i)` (the `u`-symbol
at position `i`) and `Sum.inr (v i)` (the `v`-symbol at position `i`).  This is
exactly the bipartite graph appearing in the research conjecture: a pair of
vectors is "good" when this graph *contains a cycle*.

`ContainsCycle u v` is defined as `¬ (pairGraph u v).IsAcyclic`, i.e. the graph
genuinely contains a cycle in the sense of Mathlib's `SimpleGraph` library.

## Main results

* `pairGraph_colorable` : the graph is properly `2`-colorable (it is bipartite),
  the colour being which side of the `Sum` a vertex lives on.
* `containsCycle_k_ge_four` : **the girth obstruction.**  If the pair `(u, v)`
  yields a graph containing a cycle then `4 ≤ k`.  This is sharp: a bipartite
  graph has no cycle of length `< 4`, and a cycle of length `≥ 4` needs `≥ 4`
  distinct edges, each coming from a distinct coordinate.
* `cyclicFamily_card_le_one_of_small` : consequently, for `k ≤ 3` *every*
  cycle-containing family contains at most one vector — the extremal function is
  forced to be `1` below the threshold, for **every** alphabet size `b`.

These are the unconditional, alphabet-uniform pieces of the conjecture; the exact
extremal value `N_b(k)` for large `k` is recorded as an open problem in
`FUTURE_DIRECTIONS.md`.

-- !-- Lab Notes -- !--
Hypothesis  : A pair of vectors whose bipartite graph contains a cycle cannot be
              "too short": a cycle costs edges, and edges cost coordinates.
Experiment  : Defined `pairGraph` via `fromEdgeSet`; computed that every edge runs
              between an `inl` and an `inr` vertex, hence the graph is 2-colorable.
              Combined `two_colorable_iff_forall_loop_even` (closed walks are even)
              with `IsCycle.three_le_length` (cycles have length ≥ 3) to upgrade
              the cycle length to `≥ 4`.  The cycle's `≥ 4` distinct edges inject
              into the `k` coordinates, giving `k ≥ 4`.
Analysis    : The bound `4` is *sharp* and *alphabet-independent*: the only place
              `b` enters is the codomain of the vectors, which is irrelevant to the
              girth count.  A naive attempt using only `three_le_length` gives the
              weaker `k ≥ 3`; the bipartite parity argument is what makes it sharp.
Critique    : `ContainsCycle` is the genuine graph-theoretic predicate (negation of
              `IsAcyclic`), not a hand-rolled stand-in, so the bound is faithful.
              The small-`k` corollary is non-vacuous: cyclic families do exist for
              `k ≥ 4` (see `CycleFamilies.Binary`).
Synthesis   : `containsCycle_k_ge_four` + `cyclicFamily_card_le_one_of_small`
              pin down the extremal function completely on `k ≤ 3`.
-/

open SimpleGraph Finset

namespace Catalog.Novelty.CycleFamilies

variable {b k : ℕ}

/-- The bipartite graph attached to an ordered pair of vectors `u v : Fin k → Fin b`:
vertices are two copies of the alphabet, and coordinate `i` contributes the edge
`s(inl (u i), inr (v i))`. -/
noncomputable def pairGraph (u v : Fin k → Fin b) : SimpleGraph (Fin b ⊕ Fin b) :=
  SimpleGraph.fromEdgeSet (Set.range (fun i => s(Sum.inl (u i), Sum.inr (v i))))

/-- A pair of vectors is *cycle-containing* when its bipartite graph is not acyclic. -/
def ContainsCycle (u v : Fin k → Fin b) : Prop := ¬ (pairGraph u v).IsAcyclic

/-- A family of vectors is *cyclic* when every pair of distinct members is
cycle-containing. -/
def CyclicFamily (C : Finset (Fin k → Fin b)) : Prop :=
  ∀ u ∈ C, ∀ v ∈ C, u ≠ v → ContainsCycle u v




end Catalog.Novelty.CycleFamilies


