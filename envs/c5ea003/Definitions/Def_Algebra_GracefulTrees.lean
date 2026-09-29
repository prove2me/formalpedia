-- Prove2me | Definitions.Def_Algebra_GracefulTrees
-- name    : Algebra_GracefulTrees
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:14:23.56256+00:00
-- url     : https://prove2.me/theorems/7c907b58-19fa-495d-a8bb-e0d63047753a
-- title:
--   Aether Catalog definitions — Algebra_GracefulTrees
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.GracefulTrees`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/GracefulTrees.lean by skeleton subtraction
import Mathlib

/-!
# Graceful labelings of paths and their decomposition connection

The Graceful Tree Conjecture is open.  This file formalizes the standard notion and proves
an infinite established case: every finite path is graceful.  It also proves the elementary
counting theorem used when graceful copies partition the edges of a complete graph.
-/

open Finset SimpleGraph

namespace GracefulTrees

/-- `f` gracefully labels `G` with edge parameter `m`: vertices get distinct labels in
`0,…,m`, every edge has a difference in `1,…,m`, and every such difference occurs. -/
def IsGraceful {V : Type*} (G : SimpleGraph V) (m : ℕ) (f : V → ℕ) : Prop :=
  Function.Injective f ∧
  (∀ v, f v ≤ m) ∧
  (∀ ⦃u v⦄, G.Adj u v → Nat.dist (f u) (f v) ∈ Finset.Icc 1 m) ∧
  (∀ d ∈ Finset.Icc 1 m, ∃ u v, G.Adj u v ∧ Nat.dist (f u) (f v) = d)

/-- A graph has a graceful labeling with parameter `m`. -/
def HasGracefulLabeling {V : Type*} (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ f : V → ℕ, IsGraceful G m f

/-- The usual alternating graceful labeling of the path on `n+1` vertices:
`0,n,1,n-1,2,n-2,…`. -/
def pathLabel (n : ℕ) (i : Fin (n + 1)) : ℕ :=
  if Even i.1 then i.1 / 2 else n - i.1 / 2






/-- A finite family of edge sets partitions a host graph when every host edge belongs to
exactly one member. -/
def EdgePartition {W : Type*} [Fintype W] (K : SimpleGraph W) [Fintype K.edgeSet]
    (ι : Type*) [Fintype ι] (pieces : ι → Finset (Sym2 W)) : Prop :=
  (∀ i, pieces i ⊆ K.edgeFinset) ∧
  (∀ e ∈ K.edgeFinset, ∃! i, e ∈ pieces i)


end GracefulTrees


