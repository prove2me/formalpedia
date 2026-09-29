-- Prove2me | Theorems.Thm_ToughnessOrder_isOneTough_top
-- name    : ToughnessOrder.isOneTough_top
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:53:35.734836+00:00
-- url     : https://prove2.me/theorems/fd56e660-7510-425f-b456-c89e71d30f81
-- title:
--   IsOneTough top
-- statement:
--   Formal statement of `ToughnessOrder.isOneTough_top` from the Aether Catalog (Shared). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem ToughnessOrder.isOneTough_top[Fintype V] [Nonempty V] :
--       IsOneTough (⊤ : SimpleGraph V) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/ToughnessOrder.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/ToughnessOrder.lean#L145

-- Thm stub generated from Shared/ToughnessOrder.lean
import Mathlib
import Definitions.Def_Shared_ToughnessOrder

open SimpleGraph Finset

/-!
# Toughness as an order-monotone invariant

This file packages the component-count definition of `1`-toughness as an
order-theoretic graph invariant.  Its main result, `isOneTough_mono`, says that
adding edges preserves `1`-toughness.  It also gives contrapositives and explicit
witness extraction for graphs which fail the toughness inequality.
-/

open ToughnessOrder

variable {V : Type*}



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

theorem ToughnessOrder.isOneTough_top[Fintype V] [Nonempty V] :
    IsOneTough (⊤ : SimpleGraph V) := by sorry
