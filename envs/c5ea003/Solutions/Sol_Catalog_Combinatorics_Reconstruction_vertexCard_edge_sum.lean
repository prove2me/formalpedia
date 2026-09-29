-- Prove2me | solution 1 for Catalog.Combinatorics.Reconstruction.vertexCard_edge_sum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:13:08.888327+00:00
-- url     : https://prove2.me/submissions/e56b2f5e-ac3c-43d2-8b73-e3159f408faf

-- Sol generated from Combinatorics/Reconstruction.lean
import Mathlib
import Definitions.Def_Combinatorics_Reconstruction

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















/-!
# Complement compatibility for vertex decks

Taking graph complements preserves and reflects equality of vertex-deleted decks.
-/

open Catalog.Combinatorics.Reconstruction

open SimpleGraph

variable {V W : Type*}






open Catalog.Combinatorics.Reconstruction in
theorem solution[Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ v : V, (vertexCard G v).edgeFinset.card =
      (Fintype.card V - 2) * G.edgeFinset.card := by
  -- First, establish that (vertexCard G v).edgeFinset.card equals
  -- the number of edges not containing v
  have card_equiv : ∀ v : V, (vertexCard G v).edgeFinset.card =
      (G.edgeFinset.filter (fun e => v ∉ e)).card := by
    intro v
    let embed : {x : V // x ≠ v} ↪ V := Function.Embedding.subtype _
    refine Finset.card_bij (fun e _ => e.map embed) ?_ ?_ ?_
    · intro e he
      simp only [Finset.mem_filter]
      -- Extract that e is an edge from he using Sym2.induction
      induction e using Sym2.ind with
      | _ a b =>
        have hadj : (vertexCard G v).Adj a b := by
          have := he
          simp only [SimpleGraph.mem_edgeFinset] at this
          exact this
        refine ⟨?_, ?_⟩
        · -- Show Sym2.map embed s(a, b) ∈ G.edgeFinset
          simp only [vertexCard, SimpleGraph.induce_adj] at hadj
          rw [SimpleGraph.mem_edgeFinset]
          exact hadj
        · -- Show v ∉ Sym2.map embed s(a, b)
          have ha : (a : V) ≠ v := a.property
          have hb : (b : V) ≠ v := b.property
          simp only [Sym2.map]
          rintro ⟨x, hx⟩
          have hx' : s(embed a, embed b) = s(v, x) := hx
          rw [Sym2.eq_iff] at hx'
          simp at hx'
          rcases hx' with ⟨h1, _⟩ | ⟨_, h2⟩
          · exact ha h1
          · exact hb h2
    · intro e₁ _ e₂ _ heq
      induction e₁ using Sym2.ind with
      | _ a₁ b₁ =>
        induction e₂ using Sym2.ind with
        | _ a₂ b₂ =>
          have heq' : s(embed a₁, embed b₁) = s(embed a₂, embed b₂) := heq
          rw [Sym2.eq_iff] at heq'
          rcases heq' with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [Sym2.eq_iff]
            exact Or.inl ⟨Subtype.val_injective h1, Subtype.val_injective h2⟩
          · rw [Sym2.eq_iff]
            exact Or.inr ⟨Subtype.val_injective h1, Subtype.val_injective h2⟩
    · intro e he
      simp only [Finset.mem_filter] at he
      obtain ⟨he_edge, hv_notin⟩ := he
      rw [SimpleGraph.mem_edgeFinset] at he_edge
      induction e using Sym2.ind with
      | _ x y =>
        have hadj : G.Adj x y := he_edge
        have hx : x ≠ v := by
          intro h
          apply hv_notin
          rw [h]
          simp
        have hy : y ≠ v := by
          intro h
          apply hv_notin
          rw [h]
          simp
        use Sym2.mk ⟨x, hx⟩ ⟨y, hy⟩
        refine ⟨?_, ?_⟩
        · -- Show it's in the edgeFinset of vertexCard G v
          rw [SimpleGraph.mem_edgeFinset]
          simp [vertexCard, hadj]
        · -- Show the map equals s(x, y)
          rfl
  -- Rewrite using card_equiv
  simp_rw [card_equiv]
  -- Now we need: ∑ v, #{e ∈ G.edgeFinset | v ∉ e} = (n - 2) * |G.edgeFinset|
  -- Convert #{e ∈ E | v ∉ e} to a sum
  conv_lhs =>
    arg 2
    ext v
    rw [show #{e ∈ G.edgeFinset | v ∉ e} = ∑ e ∈ G.edgeFinset, if v ∉ e then 1 else 0 by
      rw [Finset.card_filter]]
  rw [Finset.sum_comm]
  -- For each edge e = {u, v}, #{x | x ∉ e} = n - 2
  have h_card : ∀ e ∈ G.edgeFinset, ∑ x : V, (if x ∉ e then 1 else 0) = Fintype.card V - 2 := by
    intro e he
    simp only [Finset.sum_ite, Finset.sum_const, smul_eq_mul, mul_zero, add_zero, mul_one]
    -- #{x | x ∉ e} = |V \ e| = n - |e| = n - 2
    have he_card : e.toFinset.card = 2 := by
      induction e using Sym2.ind with
      | _ x y =>
        have hxy : x ≠ y := by
          have he' : s(x, y) ∈ G.edgeFinset := he
          rw [SimpleGraph.mem_edgeFinset] at he'
          exact he'.ne
        rw [Sym2.toFinset]
        rw [Sym2.toMultiset]
        simp [Multiset.toFinset, hxy]
    -- #{x | x ∉ e} = |Finset.univ \ e.toFinset| = n - 2
    have h1 : #{x : V | x ∉ e} = #{x : V | x ∉ e.toFinset} := by
      congr 1
      ext x
      simp [Sym2.mem_toFinset]
    have h2 : #{x : V | x ∉ e.toFinset} = (Finset.univ \ e.toFinset).card := by
      rw [show (Finset.univ : Finset V) \ e.toFinset = Finset.univ.filter (fun x => x ∉ e.toFinset) by
        ext x; simp]
    rw [h1, h2]
    rw [Finset.card_sdiff]
    simp [he_card]
  rw [Finset.sum_congr rfl h_card]
  simp [mul_comm]
