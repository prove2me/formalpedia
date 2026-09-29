-- Prove2me | solution 1 for PackingIsolation.isTwoPacking_singleton
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:54:03.293866+00:00
-- url     : https://prove2.me/submissions/aa2ed7f2-af60-464d-b438-b7a237b3a71f

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











open PackingIsolation in
theorem solution{G : SimpleGraph V} (v : V) :
    IsTwoPacking G ({v} : Finset V) := by
  intro a ha b hb hab
  rw [Finset.mem_singleton] at ha hb
  exact absurd (ha.trans hb.symm) hab
