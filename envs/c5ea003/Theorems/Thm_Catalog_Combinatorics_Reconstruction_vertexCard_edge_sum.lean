-- Prove2me | Theorems.Thm_Catalog_Combinatorics_Reconstruction_vertexCard_edge_sum
-- name    : Catalog.Combinatorics.Reconstruction.vertexCard_edge_sum
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:02:50.523885+00:00
-- url     : https://prove2.me/theorems/7be12989-39bc-4d70-a9fd-96c8b6a3a490
-- title:
--   Summing edge counts over the vertex-deleted cards counts every original
-- statement:
--   Summing edge counts over the vertex-deleted cards counts every original
--   edge once for each vertex outside its two endpoints.
--
--   ```lean
--   theorem Catalog.Combinatorics.Reconstruction.vertexCard_edge_sum[Fintype V] [DecidableEq V]
--       (G : SimpleGraph V) [DecidableRel G.Adj] :
--       ∑ v : V, (vertexCard G v).edgeFinset.card =
--         (Fintype.card V - 2) * G.edgeFinset.card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/Reconstruction.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/Reconstruction.lean#L86

-- Thm stub generated from Combinatorics/Reconstruction.lean
import Mathlib
import Definitions.Def_Combinatorics_Reconstruction

/-!
# Vertex-deleted decks and Kelly's counting lemma

The full reconstruction conjecture is open.  This file develops its standard
finite-graph language, proves the double-counting core of Kelly's lemma, and
proves reconstruction for the two extremal graph classes: edgeless and complete
graphs.
-/

open Catalog.Combinatorics.Reconstruction

open Finset SimpleGraph
open scoped Sym2

variable {V W U : Type*}

theorem Catalog.Combinatorics.Reconstruction.vertexCard_edge_sum[Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ v : V, (vertexCard G v).edgeFinset.card =
      (Fintype.card V - 2) * G.edgeFinset.card := by sorry
