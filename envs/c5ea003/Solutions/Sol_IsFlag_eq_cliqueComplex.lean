-- Prove2me | solution 1 for IsFlag.eq_cliqueComplex
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:19:13.91664+00:00
-- url     : https://prove2.me/submissions/84707e3d-daab-4121-9d5c-e8484a817a13

-- Sol generated from Geometry/FlagComplex.lean
import Mathlib
import Definitions.Def_Geometry_FlagComplex
/-
  Flag complexes and clique complexes of simple graphs
  ====================================================

  This file formalizes the equivalence between flag complexes and clique
  complexes of simple graphs.

  An abstract simplicial complex `K` is a *flag complex* iff a finite set of
  vertices is a face of `K` exactly when all of its distinct pairs are edges of
  the 1-skeleton of `K`.  The clique complex of a graph `G` is the simplicial
  complex whose faces are the cliques of `G`.  The main results show that the
  clique complex of any graph is flag, and that an abstract simplicial complex
  is flag if and only if it equals the clique complex of its own 1-skeleton.
-/

open Finset

variable {α : Type*} [DecidableEq α]



/-- Characterisation of adjacency in the 1-skeleton. -/
@[simp]
lemma oneSkel_adj (K : ASC α) (a b : α) :
    (oneSkel K).Adj a b ↔ a ≠ b ∧ ({a, b} : Finset α) ∈ K.faces := by
  unfold oneSkel
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h⟩
    · exact ⟨hne, by rwa [Finset.pair_comm] at h⟩
  · rintro ⟨hne, h⟩
    exact ⟨hne, Or.inl h⟩




omit [DecidableEq α] in
/-- Membership in the clique complex. -/
lemma mem_cliqueComplex (G : SimpleGraph α) (s : Finset α) :
    s ∈ (cliqueComplex G).faces ↔
      (↑s : Set α).Finite ∧ ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a ≠ b → G.Adj a b :=
  Iff.rfl








theorem solution(K : ASC α) (hK : IsFlag K) :
    K.faces = (cliqueComplex (oneSkel K)).faces := by
  ext s
  rw [mem_cliqueComplex]
  constructor
  · intro hs
    refine ⟨s.finite_toSet, ?_⟩
    intro a ha b hb hab
    rw [oneSkel_adj]
    refine ⟨hab, ?_⟩
    apply K.down_closed s hs
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  · rintro ⟨_, hclq⟩
    exact hK s (fun a ha b hb hab => hclq ha hb hab)
