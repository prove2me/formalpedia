-- Prove2me | Definitions.Def_Bridges_GraphTheory_K2UnionIndependentFree
-- name    : Bridges_GraphTheory_K2UnionIndependentFree
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:23:18.862757+00:00
-- url     : https://prove2.me/theorems/f145c37d-058a-4f68-ac77-28506e5044d3
-- title:
--   Aether Catalog definitions — Bridges_GraphTheory_K2UnionIndependentFree
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.GraphTheory.K2UnionIndependentFree`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/GraphTheory/K2UnionIndependentFree.lean by skeleton subtraction
import Mathlib

/-!
# A structural lemma for `(K₂ ∪ kK₁)`-free graphs

The forbidden induced subgraph condition has a useful equivalent local form: after fixing
an independent `k`-set, the vertices with no neighbour in that set induce an edgeless graph.
This is one of the elementary reductions used in Hamilton-connectivity arguments for this
graph class.
-/

open Finset

namespace K2UnionIndependentFree

variable {V : Type*}

/-- `G` has no induced copy of `K₂ ∪ kK₁`, expressed by naming the edge and the
`k` isolated vertices. -/
def IsK2UnionK1Free (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ ⦃u v : V⦄, G.Adj u v → ∀ I : Finset V,
    I.card = k → G.IsIndepSet (I : Set V) →
    (∀ x ∈ I, ¬ G.Adj u x ∧ ¬ G.Adj v x) → False

/-- The common antineighbourhood of a set: vertices having no neighbour in it. -/
def antiNeighborhood (G : SimpleGraph V) (A : Set V) : Set V :=
  {v | ∀ a ∈ A, ¬ G.Adj v a}







end K2UnionIndependentFree


