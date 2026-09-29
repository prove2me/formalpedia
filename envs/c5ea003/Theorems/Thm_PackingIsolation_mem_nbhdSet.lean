-- Prove2me | Theorems.Thm_PackingIsolation_mem_nbhdSet
-- name    : PackingIsolation.mem_nbhdSet
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:46:03.91291+00:00
-- url     : https://prove2.me/theorems/1ff9454b-ec05-4753-ae38-6c7390219ba2
-- title:
--   Mem nbhdSet
-- statement:
--   Formal statement of `PackingIsolation.mem_nbhdSet` from the Aether Catalog (Probability). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem PackingIsolation.mem_nbhdSet{G : SimpleGraph V} {S : Finset V} {x : V} :
--       x ∈ nbhdSet G S ↔ ∃ v ∈ S, (x = v ∨ G.Adj v x) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/Defs.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/Defs.lean#L36

-- Thm stub generated from Probability/Defs.lean
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

theorem PackingIsolation.mem_nbhdSet{G : SimpleGraph V} {S : Finset V} {x : V} :
    x ∈ nbhdSet G S ↔ ∃ v ∈ S, (x = v ∨ G.Adj v x) := by sorry
