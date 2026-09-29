-- Prove2me | solution 1 for Catalog.Combinatorics.Reconstruction.complete_reconstructible
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:15:17.677784+00:00
-- url     : https://prove2.me/submissions/047f86cc-7382-4f9c-8140-913b4149fee7

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
    (hcard : 3 ≤ Fintype.card V) (hG : G = ⊤) (hdeck : SameDeck G H) :
    Nonempty (G ≃g H) := by
  classical
  have hedge := edge_count_reconstructible G H hcard hdeck
  obtain ⟨e, _⟩ := hdeck
  have hcardVW : Fintype.card V = Fintype.card W := Fintype.card_congr e
  have hGE : G.edgeFinset = (⊤ : SimpleGraph V).edgeFinset := by
    ext x
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeFinset]
    simp [hG]
  have htopcard : H.edgeFinset.card = (⊤ : SimpleGraph W).edgeFinset.card := by
    have hV := (SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := V))
    have hW := (SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := W))
    calc
      H.edgeFinset.card = G.edgeFinset.card := hedge.symm
      _ = (⊤ : SimpleGraph V).edgeFinset.card := congrArg Finset.card hGE
      _ = (Fintype.card V).choose 2 := hV
      _ = (Fintype.card W).choose 2 := by rw [hcardVW]
      _ = (⊤ : SimpleGraph W).edgeFinset.card := hW.symm
  have hedges : H.edgeFinset = (⊤ : SimpleGraph W).edgeFinset :=
    Finset.eq_of_subset_of_card_le (SimpleGraph.edgeFinset_mono le_top) (by omega)
  have hH : H = ⊤ := SimpleGraph.edgeFinset_inj.mp hedges
  subst G
  subst H
  exact ⟨SimpleGraph.Iso.completeGraph e⟩
