-- Prove2me | Definitions.Def_Probability_Defs
-- name    : Probability_Defs
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:11:02.545994+00:00
-- url     : https://prove2.me/theorems/2e1c6b4a-52d7-4290-8aac-f2e08e5225c6
-- title:
--   Aether Catalog definitions — Probability_Defs
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.Defs`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/Defs.lean by skeleton subtraction
import Mathlib
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

namespace PackingIsolation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The closed neighbourhood `{v} ∪ N(v)` of a vertex. -/
noncomputable def closedNbhd (G : SimpleGraph V) (v : V) : Finset V :=
  insert v (G.neighborFinset v)

/-- The union of the closed neighbourhoods of the members of `S`. -/
noncomputable def nbhdSet (G : SimpleGraph V) (S : Finset V) : Finset V :=
  S.biUnion (fun v => closedNbhd G v)



/-- `S` is a *2-packing*: the closed neighbourhoods of distinct members are disjoint. -/
def IsTwoPacking (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → Disjoint (closedNbhd G u) (closedNbhd G v)

/-- `S` is *isolating*: every edge of `G` meets the closed neighbourhood of `S`. -/
def IsIsolating (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u v : V, G.Adj u v → u ∈ nbhdSet G S ∨ v ∈ nbhdSet G S

/-- `S` is *packing-isolating*: it is simultaneously a 2-packing and isolating. -/
def IsPackingIsolating (G : SimpleGraph V) (S : Finset V) : Prop :=
  IsTwoPacking G S ∧ IsIsolating G S



end PackingIsolation


