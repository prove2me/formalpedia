-- Prove2me | solution 1 for clique_pair_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:39:26.369208+00:00
-- url     : https://prove2.me/submissions/c33e931d-df80-4fe8-a012-f091c6d67bd1

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







omit [DecidableEq α] in
/-- Membership in the clique complex. -/
lemma mem_cliqueComplex (G : SimpleGraph α) (s : Finset α) :
    s ∈ (cliqueComplex G).faces ↔
      (↑s : Set α).Finite ∧ ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a ≠ b → G.Adj a b :=
  Iff.rfl








theorem solution(G : SimpleGraph α) (a b : α) (h : a ≠ b) :
    ({a, b} : Finset α) ∈ (cliqueComplex G).faces ↔ G.Adj a b := by
  rw [mem_cliqueComplex]
  constructor
  · rintro ⟨_, hclq⟩
    exact hclq (by simp) (by simp) h
  · intro hadj
    refine ⟨({a, b} : Finset α).finite_toSet, ?_⟩
    intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact hadj
    · exact hadj.symm
    · exact absurd rfl hxy
