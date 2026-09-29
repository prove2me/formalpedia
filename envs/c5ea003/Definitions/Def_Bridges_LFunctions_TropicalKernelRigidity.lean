-- Prove2me | Definitions.Def_Bridges_LFunctions_TropicalKernelRigidity
-- name    : Bridges_LFunctions_TropicalKernelRigidity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:28:36.82522+00:00
-- url     : https://prove2.me/theorems/6abbdcd2-369e-4e99-9937-86c91b2cc2c1
-- title:
--   Aether Catalog definitions — Bridges_LFunctions_TropicalKernelRigidity
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.LFunctions.TropicalKernelRigidity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/LFunctions/TropicalKernelRigidity.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tropical Kernel Rigidity: Uniqueness of Generators up to Tropical Projective Equivalence

This file establishes a canonical-form theory for tropical kernel generators
of graph Laplacians. The central result is that under support-separation
hypotheses (pairwise disjoint supports), every minimal tropical generating
family is obtained from the canonical one by tropical projective equivalence:
permutation plus pointwise constant shifts.

## Main Definitions

* `TropProjEquiv` — tropical projective equivalence of indexed function families
* `FunSupport` — support of an integer-valued function (where it's nonzero)
* `PairwiseDisjointSupports` — family with pairwise disjoint supports
* `restrictedLaplacian'` — graph Laplacian restricted to a vertex subset
* `IsHarmonicOn` — S-harmonicity for graph functions
* `harmonicKernel` — set of S-harmonic functions

## Main Results

* `tropProjEquiv_refl` — tropical projective equivalence is reflexive
* `tropProjEquiv_symm` — tropical projective equivalence is symmetric
* `tropProjEquiv_trans` — tropical projective equivalence is transitive
* `min_on_disjoint_support` — support separation forces zeroes
* `disjoint_support_no_redundancy` — generators with disjoint supports are irredundant
* `disjoint_support_unique_up_to_tropProjEquiv` — main uniqueness theorem
* `harmonic_leaf_rigidity` — harmonic functions are rigid on leaves
* `same_support_implies_same_restricted_laplacian` — matroidal invariance
* `equilibrium_iff_harmonic` — bridge to discrete potential theory

## References

* Baker, M. and Norine, S. "Riemann–Roch and Abel–Jacobi theory on a
  finite graph" (2007)
* Develin, Santos, Sturmfels, "On the rank of a tropical matrix" (2005)
-/


open Finset BigOperators

/-! ## Section 1: Tropical Projective Equivalence -/

/-- **Tropical projective equivalence** of two indexed families of ℤ-valued
    functions. Two families `F₁ F₂ : ι → V → ℤ` are tropically projectively
    equivalent if there exists a permutation `σ` of the index set and
    constants `c : ι → ℤ` such that `F₂ (σ i) v = F₁ i v + c i` for all
    `i` and `v`. -/
def TropProjEquiv {ι V : Type*} (F₁ F₂ : ι → V → ℤ) : Prop :=
  ∃ (σ : Equiv.Perm ι) (c : ι → ℤ),
    ∀ (i : ι) (v : V), F₂ (σ i) v = F₁ i v + c i




/-! ## Section 2: Function Support -/

/-- The **support** of an integer-valued function: the set of points
    where it takes nonzero values. -/
def FunSupport {V : Type*} (f : V → ℤ) : Set V := {v | f v ≠ 0}

/-- A family of functions has **pairwise disjoint supports** if the
    supports of any two distinct family members do not overlap. -/
def PairwiseDisjointSupports {ι V : Type*} (F : ι → V → ℤ) : Prop :=
  ∀ i j : ι, i ≠ j → Disjoint (FunSupport (F i)) (FunSupport (F j))

/-! ## Section 3: Support Separation Lemmas -/



/-! ## Section 4: Disjoint Support Implies Irredundancy -/


/-! ## Section 5: Tropical Span on Disjoint Supports -/


/-! ## Section 6: Main Uniqueness Theorem -/

/-
**Helper.** The support-matching function is injective when supports are
    pairwise disjoint and nontrivial.
-/

/-
**Main uniqueness theorem.** Let `F G : Fin n → V → ℤ` be families with
    pairwise disjoint supports. If they have matching support structure and
    agree pointwise on matching supports, then they are tropically projectively
    equivalent (in fact with zero constants, i.e., equal up to permutation).

    This is the tropical analogue of basis uniqueness: under the combinatorial
    separation hypothesis, generators are canonical up to reindexing.
-/

/-! ## Section 7: Graph-Theoretic Specialization -/

/-- The combinatorial graph Laplacian matrix. -/
def graphLaplacianZ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℤ :=
  fun i j =>
    if i = j then (G.degree i : ℤ)
    else if G.Adj i j then -1
    else 0


/-- The graph Laplacian restricted to a vertex subset `S`. -/
def restrictedLaplacian' {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Matrix S S ℤ :=
  fun i j => graphLaplacianZ G i.1 j.1

/-- A function `f : V → ℤ` is **S-harmonic** if the Laplacian applied to `f`,
    restricted to vertices in `S`, is zero. -/
def IsHarmonicOn {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (f : V → ℤ) : Prop :=
  ∀ v ∈ S, ∑ w : V, graphLaplacianZ G v w * f w = 0

/-- The **harmonic kernel** on `S`: the set of all S-harmonic functions. -/
def harmonicKernel {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Set (V → ℤ) :=
  {f | IsHarmonicOn G S f}




/-! ## Section 8: Matroidal Invariance -/

/-- Two graphs have the **same induced structure** on `S` if they have
    exactly the same adjacency relation on `S`. -/
def SameInducedStructure {V : Type*}
    (G₁ G₂ : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u v : V, u ∈ S → v ∈ S → (G₁.Adj u v ↔ G₂.Adj u v)



/-! ## Section 9: Discrete Potential Theory Bridge -/

/-- A **discrete potential flow** at vertex `v`. -/
def discretePotentialFlow {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (φ : V → ℤ) (v : V) : ℤ :=
  ∑ w : V, graphLaplacianZ G v w * φ w



/-! ## Section 10: Falsifiable Conjecture -/


