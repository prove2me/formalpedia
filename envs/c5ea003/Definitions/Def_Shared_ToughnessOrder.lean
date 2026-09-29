-- Prove2me | Definitions.Def_Shared_ToughnessOrder
-- name    : Shared_ToughnessOrder
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:15:14.520214+00:00
-- url     : https://prove2.me/theorems/6e94be77-afd3-4800-97fb-8af6414e31ab
-- title:
--   Aether Catalog definitions — Shared_ToughnessOrder
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.ToughnessOrder`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/ToughnessOrder.lean by skeleton subtraction
import Mathlib

open SimpleGraph Finset

/-!
# Toughness as an order-monotone invariant

This file packages the component-count definition of `1`-toughness as an
order-theoretic graph invariant.  Its main result, `isOneTough_mono`, says that
adding edges preserves `1`-toughness.  It also gives contrapositives and explicit
witness extraction for graphs which fail the toughness inequality.
-/

namespace ToughnessOrder

variable {V : Type*}

/-- Number of connected components after deleting the finite vertex set `S`. -/
noncomputable def numComp [Fintype V] (G : SimpleGraph V) (S : Finset V) : ℕ :=
  Nat.card (G.induce ((↑S : Set V)ᶜ)).ConnectedComponent

/-- A finite graph is `1`-tough when it is connected and every deletion producing
at least two components produces no more components than deleted vertices. -/
def IsOneTough [Fintype V] (G : SimpleGraph V) : Prop :=
  G.Connected ∧ ∀ S : Finset V, 2 ≤ numComp G S → numComp G S ≤ S.card

/-
Adding edges can only merge connected components, even after deleting an
arbitrary fixed set of vertices.
-/

/-
The component-count profile is antitone in the graph order.
-/

/-
Connectivity is preserved when edges are added.
-/

/-
**Main theorem: `1`-toughness is upward closed in the graph order.**
-/

/-
Equivalently, failure of `1`-toughness is downward closed.
-/

/-- The collection of `1`-tough graphs, viewed as a set in the graph lattice. -/
def oneToughGraphs [Fintype V] : Set (SimpleGraph V) := {G | IsOneTough G}

/-
Order-theoretic packaging of the main theorem: the set of tough graphs is an
upper set.
-/

/-
A connected graph which is not `1`-tough has an explicit deletion set whose
component count is both nontrivial and too large.
-/

/-
A toughness violation in a supergraph is also a violation in every subgraph:
the same deleted vertex set works.
-/

/-
For connected graphs, non-toughness descends with an explicit common witness.
-/

/-
Any tough spanning subgraph certifies toughness of the ambient graph.  This is
the abstract form of the usual Hamiltonian-cycle reduction.
-/

/-
Adding all edges of an arbitrary graph to a tough graph preserves toughness.
-/

/-
The supremum of two graphs is tough as soon as either constituent is tough.
-/

/-
On a nonempty finite vertex type, the complete graph is `1`-tough.  This
also demonstrates that the upper set of tough graphs contains the lattice top.
-/

end ToughnessOrder


