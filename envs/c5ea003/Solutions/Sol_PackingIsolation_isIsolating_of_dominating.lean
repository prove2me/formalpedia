-- Prove2me | solution 1 for PackingIsolation.isIsolating_of_dominating
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:54:02.653418+00:00
-- url     : https://prove2.me/submissions/d6f3a059-66b2-47b9-89d3-77d50557cd2e

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
theorem solution{G : SimpleGraph V} {S : Finset V}
    (h : ∀ x : V, x ∈ nbhdSet G S) : IsIsolating G S :=
  fun u _ _ => Or.inl (h u)
