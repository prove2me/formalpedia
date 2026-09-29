-- Prove2me | solution 1 for ToughnessOrder.numComp_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T02:08:47.407363+00:00
-- url     : https://prove2.me/submissions/558a80f5-572f-4061-bfe4-b41d8a5aac12

-- Sol generated from Shared/ToughnessOrder.lean
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


open ToughnessOrder in
theorem solution[Fintype V] {G H : SimpleGraph V} (h : G ≤ H)
    (S : Finset V) : numComp H S ≤ numComp G S := by
  -- Use the identity graph homomorphism between the induced subgraphs.
  set f : (G.induce ((S : Set V)ᶜ)) →g (H.induce ((S : Set V)ᶜ)) := ⟨fun x => x, fun hab => by
    exact h hab⟩
  generalize_proofs at *;
  -- Prove that the map on connected components is surjective.
  have h_surjective : Function.Surjective (SimpleGraph.ConnectedComponent.map f) := by
    rintro ⟨ x ⟩
    generalize_proofs at *;
    exact ⟨ Quot.mk _ x, rfl ⟩
  generalize_proofs at *;
  convert Nat.card_le_card_of_surjective _ h_surjective
