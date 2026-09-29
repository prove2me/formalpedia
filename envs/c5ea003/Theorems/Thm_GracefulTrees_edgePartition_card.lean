-- Prove2me | Theorems.Thm_GracefulTrees_edgePartition_card
-- name    : GracefulTrees.edgePartition_card
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:33:44.006436+00:00
-- url     : https://prove2.me/theorems/0e6bd879-d598-44fd-82f1-599a402b1e01
-- title:
--   Decomposition counting theorem.
-- statement:
--   **Decomposition counting theorem.** If copies partition a finite host graph and every
--   copy has `m` edges, then the host has `|ι|·m` edges.  In particular this supplies the
--   necessary divisibility condition in complete-graph decomposition constructions arising
--   from graceful labelings.
--
--   ```lean
--   theorem GracefulTrees.edgePartition_card{W : Type*} [Fintype W] [DecidableEq W]
--       (K : SimpleGraph W) [Fintype K.edgeSet] (ι : Type*) [Fintype ι]
--       (pieces : ι → Finset (Sym2 W)) (m : ℕ)
--       (hpart : EdgePartition K ι pieces) (hcard : ∀ i, (pieces i).card = m) :
--       K.edgeFinset.card = Fintype.card ι * m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/GracefulTrees.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/GracefulTrees.lean#L112

-- Thm stub generated from Algebra/GracefulTrees.lean
import Mathlib
import Definitions.Def_Algebra_GracefulTrees

/-!
# Graceful labelings of paths and their decomposition connection

The Graceful Tree Conjecture is open.  This file formalizes the standard notion and proves
an infinite established case: every finite path is graceful.  It also proves the elementary
counting theorem used when graceful copies partition the edges of a complete graph.
-/

open Finset SimpleGraph

open GracefulTrees

theorem GracefulTrees.edgePartition_card{W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W) [Fintype K.edgeSet] (ι : Type*) [Fintype ι]
    (pieces : ι → Finset (Sym2 W)) (m : ℕ)
    (hpart : EdgePartition K ι pieces) (hcard : ∀ i, (pieces i).card = m) :
    K.edgeFinset.card = Fintype.card ι * m := by sorry
