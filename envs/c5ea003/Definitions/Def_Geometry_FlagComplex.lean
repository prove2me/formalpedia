-- Prove2me | Definitions.Def_Geometry_FlagComplex
-- name    : Geometry_FlagComplex
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:16:32.707975+00:00
-- url     : https://prove2.me/theorems/9ba3eae9-78a2-48d1-9585-e5c372e64074
-- title:
--   Aether Catalog definitions — Geometry_FlagComplex
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.FlagComplex`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/FlagComplex.lean by skeleton subtraction
import Mathlib
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

/-- An abstract simplicial complex on `α`. -/
structure ASC (α : Type*) where
  /-- The set of faces of the complex. -/
  faces : Set (Finset α)
  /-- Faces are downward closed: every subset of a face is a face. -/
  down_closed : ∀ s ∈ faces, ∀ t ⊆ s, t ∈ faces
  /-- Every vertex appearing in some face is itself a (singleton) face. -/
  singletons_mem : ∀ a, (∃ s ∈ faces, a ∈ s) → ({a} : Finset α) ∈ faces

/-- The 1-skeleton of an abstract simplicial complex: vertices `a` and `b` are
adjacent precisely when `a ≠ b` and `{a, b}` is a face. -/
def oneSkel (K : ASC α) : SimpleGraph α :=
  SimpleGraph.fromRel (fun a b => ({a, b} : Finset α) ∈ K.faces)




/-- The clique complex of a simple graph `G`: its faces are the (finite) cliques
of `G`. -/
def cliqueComplex (G : SimpleGraph α) : ASC α where
  faces := {s : Finset α |
    (↑s : Set α).Finite ∧ ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a ≠ b → G.Adj a b}
  down_closed := by
    rintro s ⟨_, hs⟩ t ht
    exact ⟨t.finite_toSet, fun a ha b hb hab => hs (ht ha) (ht hb) hab⟩
  singletons_mem := by
    rintro a _
    refine ⟨({a} : Finset α).finite_toSet, ?_⟩
    intro x hx y hy hxy
    simp only [Finset.mem_singleton] at hx hy
    subst hx; subst hy
    exact absurd rfl hxy


/-- The flag property of an abstract simplicial complex: a finite vertex set all
of whose distinct pairs are edges of the 1-skeleton is itself a face. -/
def IsFlag (K : ASC α) : Prop :=
  ∀ s : Finset α,
    (∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a ≠ b → (oneSkel K).Adj a b) → s ∈ K.faces


