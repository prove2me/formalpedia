-- Prove2me | Definitions.Def_Applications_CayleyStability_Embedding
-- name    : Applications_CayleyStability_Embedding
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:39:14.784368+00:00
-- url     : https://prove2.me/theorems/66a4b6d4-708b-48ff-97cc-9dc919a271a8
-- title:
--   Aether Catalog definitions — Applications_CayleyStability_Embedding
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.CayleyStability.Embedding`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/CayleyStability/Embedding.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026. All rights reserved.

# Stability of Cayley Digraphs — The Expected-Automorphism Embedding

This file develops a Lean framework for the *stability* of Cayley digraphs and
proves the universally valid half of the stability statement: the **expected
automorphisms always embed**.

## Setting

For a finite abelian group `G` and a connection set `S ⊆ G`, the Cayley digraph
`Cay(G, S)` has vertex set `G` and an arc `g → h` whenever `h - g ∈ S`
(`cayAdj`).  The *tensor product with the complete digraph `K₂`* (equivalently,
the bipartite double cover) has vertex set `G × Bool` with an arc
`(g,a) → (h,b)` whenever `h - g ∈ S` and `a ≠ b` (`dcAdj`).

A digraph `X` is **stable** when `Aut(X ⊗ K₂) ≅ Aut(X) × Aut(K₂)`.  Since
`Aut(K₂) = Sym(Bool) = Equiv.Perm Bool`, there is a canonical homomorphism
`expectedHom : Aut(Cay(G,S)) × Perm Bool →* Aut(Cay(G,S) ⊗ K₂)` given by
`(σ, π) ↦ σ ×ₚ π`.  Stability is precisely the assertion that this map is an
*isomorphism*; one direction — injectivity — holds for **every** digraph and is
the content of `expectedHom_injective`.

We additionally show (`dcCayleyIso`) that the double cover is itself a Cayley
digraph, over the group `G × ℤ/2` with connection set `S × {1}`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): The map sending an automorphism `σ` of the base
digraph and a permutation `π` of the two layers to the product permutation
`σ ×ₚ π` of the double cover is an injective group homomorphism into the
automorphism group of the double cover, for *every* connection set (no oddness,
connectivity, or twin-freeness needed).

Experiment (Experimenter): Formalised `AutRel` (the automorphism group of a
relation, as a subgroup of `Equiv.Perm`), proved `prodCongr_mem` (product
permutations are automorphisms of the double cover) and bundled the map into
`expectedHom`.  Injectivity reduces to evaluating at `(g, false)` and `(0, b)`.

Analysis (Analyst): Injectivity needs `Nonempty G` (supplied by the additive
identity) to recover the `Perm Bool` factor; without a base vertex the second
factor cannot be detected.  The product structure also reveals the double cover
*is* a Cayley digraph over `G × ℤ/2` — recorded as `dcCayleyIso`.

Critique (Critic): The statements use real group/permutation machinery
(`Subgroup`, `MonoidHom`, `prodCongr`), evaluation arguments, and are not
definitional.  Surjectivity of `expectedHom` — the *hard* half, true exactly for
connected twin-free Cayley digraphs of odd order — is deliberately NOT claimed
here; it is studied in `OddOrderNecessity.lean` where the odd-order hypothesis
is shown to be necessary.

Synthesis (PI): `expectedHom_injective` is the universal backbone of any
stability proof; `dcCayleyIso` shows the double cover stays inside the same
category of objects, enabling inductive/structural attacks on the open half.
-- !-- end Lab Notes -- !--
-/

open Equiv

namespace CayleyStability

variable {G : Type*} [AddCommGroup G]

/-- Adjacency of the Cayley digraph `Cay(G, S)`: an arc `g → h` exists iff
`h - g ∈ S`. -/
def cayAdj (S : Set G) (g h : G) : Prop := h - g ∈ S

/-- Adjacency of the tensor product `Cay(G, S) ⊗ K₂` (the bipartite double
cover): an arc `(g,a) → (h,b)` exists iff `h - g ∈ S` and `a ≠ b`. -/
def dcAdj (S : Set G) (p q : G × Bool) : Prop := (q.1 - p.1 ∈ S) ∧ (p.2 ≠ q.2)

/-- The automorphism group of a binary relation `r`, realised as a subgroup of
the permutation group of the vertex set. -/
def AutRel {V : Type*} (r : V → V → Prop) : Subgroup (Equiv.Perm V) where
  carrier := {σ | ∀ a b, r (σ a) (σ b) ↔ r a b}
  one_mem' := by intro a b; simp
  mul_mem' := by
    intro σ τ hσ hτ a b
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    rw [hσ, hτ]
  inv_mem' := by
    intro σ hσ a b
    have h := hσ (σ⁻¹ a) (σ⁻¹ b)
    simpa using h.symm


/-- A product permutation `σ ×ₚ π` (with `σ` an automorphism of the base
digraph and `π` an arbitrary permutation of the two layers) is an automorphism
of the double cover. -/
lemma prodCongr_mem (S : Set G) (σ : Equiv.Perm G) (π : Equiv.Perm Bool)
    (hσ : σ ∈ AutRel (cayAdj S)) : σ.prodCongr π ∈ AutRel (dcAdj S) := by
  intro a b
  have hkey := hσ a.1 b.1
  simp only [cayAdj] at hkey
  simp only [dcAdj, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd]
  rw [hkey]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, fun h => h2 (by rw [h])⟩,
         fun ⟨h1, h2⟩ => ⟨h1, fun h => h2 (π.injective h)⟩⟩

/-- The canonical embedding of the *expected* automorphism group
`Aut(Cay(G,S)) × Aut(K₂)` into `Aut(Cay(G,S) ⊗ K₂)`, sending `(σ, π)` to the
product permutation `σ ×ₚ π`.  Stability of `Cay(G,S)` is the assertion that
this homomorphism is surjective. -/
def expectedHom (S : Set G) :
    (AutRel (cayAdj S)) × (Equiv.Perm Bool) →* (AutRel (dcAdj S)) where
  toFun p := ⟨(p.1 : Equiv.Perm G).prodCongr p.2, prodCongr_mem S _ _ p.1.2⟩
  map_one' := by apply Subtype.ext; ext x <;> simp
  map_mul' a b := by apply Subtype.ext; ext x <;> simp [Subgroup.coe_mul]





end CayleyStability


