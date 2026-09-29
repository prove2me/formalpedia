-- Prove2me | Theorems.Thm_PackingIsolation_isIsolating_of_dominating
-- name    : PackingIsolation.isIsolating_of_dominating
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:46:04.687979+00:00
-- url     : https://prove2.me/theorems/e374ac1d-148c-4007-8ea0-99a87b6bc36a
-- title:
--   A dominating set (one whose closed neighbourhood is everything) is isolating.
-- statement:
--   A dominating set (one whose closed neighbourhood is everything) is isolating.
--
--   ```lean
--   theorem PackingIsolation.isIsolating_of_dominating{G : SimpleGraph V} {S : Finset V}
--       (h : ∀ x : V, x ∈ nbhdSet G S) : IsIsolating G S := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/Defs.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/Defs.lean#L59

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

theorem PackingIsolation.isIsolating_of_dominating{G : SimpleGraph V} {S : Finset V}
    (h : ∀ x : V, x ∈ nbhdSet G S) : IsIsolating G S := by sorry
