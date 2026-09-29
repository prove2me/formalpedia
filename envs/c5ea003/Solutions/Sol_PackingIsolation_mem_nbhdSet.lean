-- Prove2me | solution 1 for PackingIsolation.mem_nbhdSet
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:54:03.888414+00:00
-- url     : https://prove2.me/submissions/ba295044-b466-438a-8c9d-08da4ac1b1da

-- Sol generated from Probability/Defs.lean
import Mathlib
import Definitions.Def_Probability_Defs
/-
  Packing-Isolating Sets — basic definitions

  This file supplies the definitions used by `Probability.Constructions`
  (packing-isolating sets in block graphs).

  For a finite simple graph `G` and a vertex `v`, `closedNbhd G v` is the closed
  neighbourhood `{v} ∪ N(v)`, and `nbhdSet G S = ⋃_{v ∈ S} closedNbhd G v`.

  * `IsTwoPacking G S` : the closed neighbourhoods of distinct members of `S` are
    pairwise disjoint (equivalently, distinct members of `S` are at distance `≥ 3`).
  * `IsIsolating G S` : every edge of `G` has an endpoint in `nbhdSet G S`, i.e.
    deleting `nbhdSet G S` leaves no edges.
  * `IsPackingIsolating G S` : both conditions hold.
-/

open Finset SimpleGraph
open scoped Classical

open PackingIsolation

variable {V : Type*} [Fintype V] [DecidableEq V]



@[simp] theorem mem_closedNbhd {G : SimpleGraph V} {v x : V} :
    x ∈ closedNbhd G v ↔ x = v ∨ G.Adj v x := by
  simp [closedNbhd]








open PackingIsolation in
theorem solution{G : SimpleGraph V} {S : Finset V} {x : V} :
    x ∈ nbhdSet G S ↔ ∃ v ∈ S, (x = v ∨ G.Adj v x) := by
  simp [nbhdSet, mem_closedNbhd]
