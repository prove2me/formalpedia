-- Prove2me | solution 1 for Catalog.Combinatorics.Reconstruction.edgeless_reconstructible
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:15:18.342734+00:00
-- url     : https://prove2.me/submissions/7a8de1a0-3370-4261-94a3-9575e120b0ff

-- Sol generated from Combinatorics/Reconstruction.lean
import Mathlib
import Definitions.Def_Combinatorics_Reconstruction
import Theorems.Thm_Catalog_Combinatorics_Reconstruction_vertexCard_edge_sum

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









/-- Isomorphic finite graphs have equal numbers of edges. -/
theorem edge_count_eq_of_iso [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : G ≃g H) : G.edgeFinset.card = H.edgeFinset.card := by
  exact e.card_edgeFinset_eq


/-- The number of edges is reconstructible from the deck for graphs with at
least three vertices.  This is the `K₂` instance of Kelly's principle. -/
theorem edge_count_reconstructible [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hcard : 3 ≤ Fintype.card V) (hdeck : SameDeck G H) :
    G.edgeFinset.card = H.edgeFinset.card := by
  obtain ⟨e, he⟩ := hdeck
  have hVW : Fintype.card V = Fintype.card W := Fintype.card_congr e
  have hsums : (∑ v : V, (vertexCard G v).edgeFinset.card) =
      ∑ w : W, (vertexCard H w).edgeFinset.card := by
    rw [← e.sum_comp]
    apply Finset.sum_congr rfl
    intro v _
    exact edge_count_eq_of_iso (Classical.choice (he v))
  rw [vertexCard_edge_sum G, vertexCard_edge_sum H, ← hVW] at hsums
  exact Nat.eq_of_mul_eq_mul_left (by omega) hsums




/-!
# Complement compatibility for vertex decks

Taking graph complements preserves and reflects equality of vertex-deleted decks.
-/

open Catalog.Combinatorics.Reconstruction

open SimpleGraph

variable {V W : Type*}






open Catalog.Combinatorics.Reconstruction in
theorem solution[Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hcard : 3 ≤ Fintype.card V) (hG : G = ⊥) (hdeck : SameDeck G H) :
    Nonempty (G ≃g H) := by
  classical
  have hedge := edge_count_reconstructible G H hcard hdeck
  obtain ⟨e, _⟩ := hdeck
  have hGE : G.edgeFinset = ∅ := by
    ext x
    rw [SimpleGraph.mem_edgeFinset]
    simp [hG]
  have hzero : H.edgeFinset.card = 0 := by
    rw [← hedge, hGE, Finset.card_empty]
  have hH : H = ⊥ := (SimpleGraph.edgeFinset_eq_empty.mp (Finset.card_eq_zero.mp hzero))
  subst G
  subst H
  exact ⟨⟨e, by simp⟩⟩
