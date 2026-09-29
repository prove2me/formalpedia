-- Prove2me | Theorems.Thm_K2UnionIndependentFree_free_iff_antineighborhood_independent
-- name    : K2UnionIndependentFree.free_iff_antineighborhood_independent
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:49:53.756507+00:00
-- url     : https://prove2.me/theorems/576e74e5-664e-4812-b1ea-4496e5861c62
-- title:
--   Exact local characterization of the forbidden induced-subgraph condition.
-- statement:
--   Exact local characterization of the forbidden induced-subgraph condition. A graph is
--   `(K₂ ∪ kK₁)`-free precisely when the common antineighbourhood of every independent
--   `k`-set is independent.
--
--   ```lean
--   theorem K2UnionIndependentFree.free_iff_antineighborhood_independent{G : SimpleGraph V} {k : ℕ} :
--       IsK2UnionK1Free G k ↔
--         ∀ I : Finset V, I.card = k → G.IsIndepSet (I : Set V) →
--           G.IsIndepSet (antiNeighborhood G (I : Set V)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/GraphTheory/K2UnionIndependentFree.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/GraphTheory/K2UnionIndependentFree.lean#L42

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

theorem K2UnionIndependentFree.free_iff_antineighborhood_independent{G : SimpleGraph V} {k : ℕ} :
    IsK2UnionK1Free G k ↔
      ∀ I : Finset V, I.card = k → G.IsIndepSet (I : Set V) →
        G.IsIndepSet (antiNeighborhood G (I : Set V)) := by sorry
