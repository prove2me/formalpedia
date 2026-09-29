-- Prove2me | solution 1 for ToughnessOrder.isOneTough_top
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T02:08:46.752741+00:00
-- url     : https://prove2.me/submissions/c9a88bbb-06d7-436e-9519-f12d7369cd65

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
theorem solution[Fintype V] [Nonempty V] :
    IsOneTough (⊤ : SimpleGraph V) := by
  refine' ⟨ _, _ ⟩;
  · simp +decide [ SimpleGraph.connected_iff_exists_forall_reachable ];
  · intro S;
    -- The induced graph on the complement of S is complete, hence it is preconnected.
    have h_preconnected : (⊤ : SimpleGraph V).induce ((↑S : Set V)ᶜ) |>.Preconnected := by
      intro v w; by_cases hvw : v = w <;> simp +decide [ hvw ] ;
    have h_subsingleton : Subsingleton ((⊤ : SimpleGraph V).induce ((↑S : Set V)ᶜ)).ConnectedComponent := by
      exact Preconnected.subsingleton_connectedComponent h_preconnected
    have h_card_le_one : Nat.card ((⊤ : SimpleGraph V).induce ((↑S : Set V)ᶜ)).ConnectedComponent ≤ 1 := by
      exact Finite.card_le_one_iff_subsingleton.mpr h_subsingleton
    exact fun h => absurd h ( not_le_of_gt ( lt_of_le_of_lt h_card_le_one ( by decide ) ) )
