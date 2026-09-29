-- Prove2me | Theorems.Thm_K2UnionIndependentFree_zero_iff_bot
-- name    : K2UnionIndependentFree.zero_iff_bot
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:50:01.276329+00:00
-- url     : https://prove2.me/theorems/6205b252-3dba-4b7c-9039-945e6cad3912
-- title:
--   For `k = 0`, the condition says exactly that the graph has no edges.
-- statement:
--   For `k = 0`, the condition says exactly that the graph has no edges.
--
--   ```lean
--   theorem K2UnionIndependentFree.zero_iff_bot(G : SimpleGraph V) :
--       IsK2UnionK1Free G 0 ↔ G = ⊥ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/GraphTheory/K2UnionIndependentFree.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/GraphTheory/K2UnionIndependentFree.lean#L83

-- Thm stub generated from Bridges/GraphTheory/K2UnionIndependentFree.lean
import Mathlib
import Definitions.Def_Bridges_GraphTheory_K2UnionIndependentFree

/-!
# A structural lemma for `(K₂ ∪ kK₁)`-free graphs

The forbidden induced subgraph condition has a useful equivalent local form: after fixing
an independent `k`-set, the vertices with no neighbour in that set induce an edgeless graph.
This is one of the elementary reductions used in Hamilton-connectivity arguments for this
graph class.
-/

open Finset

open K2UnionIndependentFree

variable {V : Type*}

theorem K2UnionIndependentFree.zero_iff_bot(G : SimpleGraph V) :
    IsK2UnionK1Free G 0 ↔ G = ⊥ := by sorry
