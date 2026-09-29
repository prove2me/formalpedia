-- Prove2me | Definitions.Def_Geometry_RamseyTheory_CliqueComplexFlag
-- name    : Geometry_RamseyTheory_CliqueComplexFlag
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:52:09.59827+00:00
-- url     : https://prove2.me/theorems/4d40d1ac-5a33-4fcd-8d86-54829fae1e1d
-- title:
--   Aether Catalog definitions — Geometry_RamseyTheory_CliqueComplexFlag
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.RamseyTheory.CliqueComplexFlag`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/RamseyTheory/CliqueComplexFlag.lean by skeleton subtraction
import Mathlib
/-
# Clique Complexes, Flag Complexes, and the Vietoris–Rips Filtration

This file develops, from scratch, a lightweight theory of abstract simplicial
complexes (`ASC`) and the clique-complex construction on simple graphs, together
with the flag-complex characterization, the Vietoris–Rips filtration, and a
Turán-style bound on the `f`-vector.

## Main results

* `isClique_pair`            — a two-element set is a clique iff its endpoints are adjacent.
* `cliqueComplex_isFlag`     — every clique complex is a flag complex.
* `oneSkeleton_cliqueComplex`— the one-skeleton of `Δ(G)` is exactly `G`.
* `flag_eq_cliqueComplex`    — every flag complex *with all singletons* is the clique
                               complex of its own one-skeleton (the converse direction).
* `vietorisRips_mono`        — the Vietoris–Rips complex is monotone in the scale `ε`.
* `cliqueComplex_fVector_le_choose` — `f_k(Δ(G)) ≤ C(n, k+1)` (Turán-style upper bound).
* `flag_not_cliqueComplex_without_singletons` — the singleton hypothesis in
                               `flag_eq_cliqueComplex` cannot be dropped (counterexample).

-- !-- Lab Notebook -- !--
Hypothesis: the clique-complex and one-skeleton constructions form an
  adjunction-like pair on simple graphs, with flag complexes the image of `Δ`.
Result: proved both directions, with the precise side condition (all singletons
  present) isolated by an explicit counterexample on `Bool`.
Insight: the entire theory pivots on the single fact `isClique_pair`
  ("a 2-clique is an edge"); the forward direction is downward closure and the
  converse rebuilds a face from its edges via the flag axiom.
Failure analysis: the naive converse (drop the singleton hypothesis) is FALSE —
  clique complexes always contain every singleton, but a flag complex need not,
  witnessed by the trivial complex `{∅}` whose one-skeleton is the empty graph.
-- !-- Lab Notebook -- !--
-/

namespace CliqueComplexFlag

open scoped Classical

universe u
variable {V : Type u}

/-- An **abstract simplicial complex** on a vertex type `V`: a set of finite faces
that is closed under taking subsets. -/
structure ASC (V : Type u) where
  /-- The set of faces of the complex. -/
  faces : Set (Finset V)
  /-- Downward closure: any subset of a face is a face. -/
  down_closed : ∀ ⦃s t : Finset V⦄, s ⊆ t → t ∈ faces → s ∈ faces

namespace ASC


end ASC

/-! ## The clique complex of a simple graph -/

/-- The **clique complex** `Δ(G)`: faces are the finite cliques of `G`. -/
def cliqueComplex (G : SimpleGraph V) : ASC V where
  faces := {s : Finset V | G.IsClique (↑s : Set V)}
  down_closed := by
    intro s t hst ht
    exact ht.subset (by exact_mod_cast hst)



/-! ## The one-skeleton of a complex -/

/-- The **one-skeleton** graph of a complex: `u` and `v` are adjacent iff they are
distinct and `{u, v}` is a face. -/
def oneSkeleton (K : ASC V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ({u, v} : Finset V) ∈ K.faces
  symm := by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    have : ({v, u} : Finset V) = ({u, v} : Finset V) := by
      ext x; simp [or_comm]
    rw [this]; exact h.2
  loopless := ⟨fun u h => h.1 rfl⟩



/-! ## Flag complexes -/

/-- A complex `K` is a **flag complex** if every finite vertex set, all of whose
singletons are faces and all of whose pairs are faces, is itself a face. -/
def IsFlag (K : ASC V) : Prop :=
  ∀ s : Finset V,
    (∀ u ∈ s, ({u} : Finset V) ∈ K.faces) →
    (∀ u ∈ s, ∀ v ∈ s, u ≠ v → ({u, v} : Finset V) ∈ K.faces) →
    s ∈ K.faces



/-! ## The Vietoris–Rips complex -/

/-- The **Vietoris–Rips graph** of a dissimilarity `d` at scale `ε`: distinct
vertices are adjacent when both directed dissimilarities are `≤ ε` (this symmetric
form needs no symmetry hypothesis on `d`). -/
def vietorisRipsGraph (d : V → V → ℝ) (ε : ℝ) : SimpleGraph V where
  Adj u v := u ≠ v ∧ d u v ≤ ε ∧ d v u ≤ ε
  symm := by intro u v h; exact ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := ⟨fun u h => h.1 rfl⟩

/-- The **Vietoris–Rips complex** is the clique complex of the Vietoris–Rips graph. -/
def vietorisRips (d : V → V → ℝ) (ε : ℝ) : ASC V :=
  cliqueComplex (vietorisRipsGraph d ε)


/-! ## The f-vector and a Turán-style bound -/

/-- The **`f`-vector** of a complex on a finite vertex type: `fVector K k` counts the
faces of cardinality `k + 1` (the `k`-dimensional faces). -/
noncomputable def fVector [Fintype V] (K : ASC V) (k : ℕ) : ℕ :=
  ((Finset.univ.powersetCard (k + 1)).filter (fun s => s ∈ K.faces)).card


/-! ## The singleton hypothesis is necessary -/

/-- The trivial complex on `Bool` whose only face is the empty set. -/
def trivialComplex : ASC Bool where
  faces := {∅}
  down_closed := by
    intro s t hst ht
    simp only [Set.mem_singleton_iff] at ht ⊢
    subst ht
    exact Finset.subset_empty.1 hst


end CliqueComplexFlag


