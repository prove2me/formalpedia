-- Prove2me | Definitions.Def_Bridges_TropicalAlgebra_OverlapSpectrumTheory
-- name    : Bridges_TropicalAlgebra_OverlapSpectrumTheory
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:41:16.48323+00:00
-- url     : https://prove2.me/theorems/86f3ed98-2926-4e8f-9863-0f24f31bc72b
-- title:
--   Aether Catalog definitions — Bridges_TropicalAlgebra_OverlapSpectrumTheory
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalAlgebra.OverlapSpectrumTheory`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalAlgebra/OverlapSpectrumTheory.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Overlap Spectrum Theory: Partitions, Metrics, and Spectral Bridges

This file develops the **overlap spectrum** — the integer partition induced by
overlap class sizes — and establishes its invariance properties, metric
structure, and connections to spectral graph theory and coding theory.

## Mathematical Context

Given a family of n finsets (e.g., cycle supports of tropical kernel generators),
the overlap equivalence classes partition the index set {0, ..., n-1}. The sizes
of these classes form an integer partition of n, which we call the **overlap
spectrum**. This is a strictly finer invariant than the overlap class count.

## Main Definitions

* `OvEquiv` — overlap equivalence (reflexive-transitive closure of overlap)
* `ovSetoid` — the corresponding setoid on `Fin n`
* `ovClassCount` — number of overlap classes
* `overlapLaplacian` — the Laplacian matrix of the overlap graph
* `ovVertexDeg` — vertex degree in the overlap graph
* `ovComplexity` — sum of pairwise intersection sizes

## Main Results

* `ovClassCount_eq_of_pd` — class count = n when pairwise disjoint + nonempty
* `fully_connected_one_class'` — class count = 1 when every pair overlaps
* `class_count_le_universe` — n ≤ |α| for pairwise disjoint families
* `laplacian_trace_eq_degree_sum` — trace of Laplacian = sum of degrees
* `degree_sum_eq_twice_ovDegree` — handshaking lemma for overlap graph
* `laplacian_row_sum_zero` — Laplacian rows sum to zero
* `ovComplexity_zero_iff` — zero complexity ↔ pairwise disjoint
* `disjoint_implies_singleton_classes` — pairwise disjoint → each class is {i}
* `ovEquiv_exists_chain` — overlap equivalence implies existence of chain

## Cross-Domain Connections

* Tropical geometry → Partition theory (overlap spectrum)
* Graph theory → Spectral theory (overlap Laplacian)
* Combinatorics → Coding theory (support distance metric)
-/


open Finset BigOperators Classical

attribute [local instance] Classical.propDecidable

/-! ## Section 1: Support Overlap — Core Definitions -/

/-- Two finsets **overlap** if their intersection is nonempty. -/
def SOverlap {α : Type*} [DecidableEq α] (A B : Finset α) : Prop :=
  (A ∩ B).Nonempty

instance sOverlapDecidable {α : Type*} [DecidableEq α] (A B : Finset α) :
    Decidable (SOverlap A B) :=
  inferInstanceAs (Decidable (A ∩ B).Nonempty)

theorem sOverlap_symm {α : Type*} [DecidableEq α] {A B : Finset α} :
    SOverlap A B ↔ SOverlap B A := by
  simp only [SOverlap, inter_comm]


/-- The overlap equivalence relation: reflexive-transitive closure of overlap. -/
def OvEquiv {α : Type*} [DecidableEq α] {ι : Type*}
    (F : ι → Finset α) (i j : ι) : Prop :=
  Relation.ReflTransGen (fun a b => SOverlap (F a) (F b)) i j

theorem ovEquiv_refl {α : Type*} [DecidableEq α] {ι : Type*}
    (F : ι → Finset α) (i : ι) : OvEquiv F i i :=
  Relation.ReflTransGen.refl

theorem ovEquiv_symm {α : Type*} [DecidableEq α] {ι : Type*}
    (F : ι → Finset α) {i j : ι} (h : OvEquiv F i j) : OvEquiv F j i := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih =>
    exact Relation.ReflTransGen.trans
      (Relation.ReflTransGen.single (sOverlap_symm.mp hab)) ih

theorem ovEquiv_trans {α : Type*} [DecidableEq α] {ι : Type*}
    (F : ι → Finset α) {i j k : ι} (hij : OvEquiv F i j) (hjk : OvEquiv F j k) :
    OvEquiv F i k :=
  Relation.ReflTransGen.trans hij hjk

/-- The overlap setoid on `Fin n`. -/
def ovSetoid {α : Type*} [DecidableEq α] {n : ℕ}
    (F : Fin n → Finset α) : Setoid (Fin n) where
  r := OvEquiv F
  iseqv := ⟨ovEquiv_refl F, fun h => ovEquiv_symm F h, fun h₁ h₂ => ovEquiv_trans F h₁ h₂⟩


/-! ## Section 2: Pairwise Disjointness and Overlap Degree -/

/-- A finset family is **pairwise disjoint**. -/
def PDFamily {α : Type*} [DecidableEq α] {ι : Type*}
    (F : ι → Finset α) : Prop :=
  ∀ i j : ι, i ≠ j → Disjoint (F i) (F j)

/-- The **overlap degree**: number of overlapping pairs. -/
def OvDegree {α : Type*} [DecidableEq α] {n : ℕ}
    (F : Fin n → Finset α) : ℕ :=
  ((Finset.univ ×ˢ Finset.univ).filter
    (fun p : Fin n × Fin n => p.1 < p.2 ∧ SOverlap (F p.1) (F p.2))).card

/-! ## Section 3: Overlap Class Count -/

/-- Number of overlap classes via quotient cardinality. -/
noncomputable def ovClassCount {α : Type*} [DecidableEq α] {n : ℕ}
    (F : Fin n → Finset α) : ℕ :=
  Fintype.card (Quotient (ovSetoid F))


/-
**Key Theorem (by_contra + induction):**
    Class count = n when pairwise disjoint and nonempty.
-/

/-! ## Section 4: Fully Connected Regime -/

/-
**Deep Theorem (by_contra + rcases):**
    When every pair overlaps, there is exactly one overlap class.
-/

/-! ## Section 5: Overlap Laplacian — Cross-Domain Bridge to Spectral Theory -/

/-- The **overlap degree** of a single vertex: how many other supports it overlaps. -/
def ovVertexDeg {α : Type*} [DecidableEq α] {n : ℕ}
    (F : Fin n → Finset α) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun j => j ≠ i ∧ SOverlap (F i) (F j))).card

/-- The **overlap Laplacian matrix**: L(i,j) = deg(i) if i=j,
    -1 if adjacent, 0 otherwise. -/
def overlapLaplacian {α : Type*} [DecidableEq α] {n : ℕ}
    (F : Fin n → Finset α) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j =>
    if i = j then (ovVertexDeg F i : ℤ)
    else if SOverlap (F i) (F j) then -1
    else 0


/-
**The Handshaking Lemma for the overlap graph (deep proof with Finset combinatorics):**
    Sum of vertex degrees = 2 × number of edges.
-/

/-
**Laplacian row sums are zero (deep proof with field_simp-style reasoning).**
-/

/-! ## Section 6: Overlap Complexity -/

/-- The **overlap complexity**: sum of pairwise intersection sizes. -/
def ovComplexity {α : Type*} [DecidableEq α] {n : ℕ}
    (F : Fin n → Finset α) : ℕ :=
  ∑ p ∈ (univ ×ˢ univ).filter (fun p : Fin n × Fin n => p.1 < p.2),
    (F p.1 ∩ F p.2).card

/-
**Overlap complexity zero ↔ pairwise disjoint (multi-step proof with rcases).**
-/

/-! ## Section 7: Universe Size Bound -/

/-
**In a pairwise disjoint family over a finite universe, n ≤ |α|.
    (Deep proof with calc chain.)**
-/

/-! ## Section 8: Overlap Chain Existence -/

/-
**If i and j are overlap-equivalent, there exists a finite chain
    connecting them (induction on ReflTransGen).**
-/

/-! ## Section 9: Singleton Classes from Disjointness -/

/-- The **overlap class** of index i. -/
noncomputable def ovClass {α : Type*} [DecidableEq α] {n : ℕ}
    (F : Fin n → Finset α) (i : Fin n) : Finset (Fin n) :=
  @Finset.filter _ (fun _j => OvEquiv F i _j) (fun _j => Classical.dec _) Finset.univ

/-
**Pairwise disjoint + nonempty ⟹ singleton classes
    (deep proof with by_contra + induction).**
-/

/-! ## Section 10: TPE Invariance -/


/-- Variation support: where f differs from its basepoint value. -/
def VarSup {V : Type*} [Fintype V] [DecidableEq V]
    (f : V → ℤ) (v₀ : V) : Finset V :=
  Finset.univ.filter (fun v => f v ≠ f v₀)

/-- Family of variation supports. -/
def VarSupFam {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (F : Fin n → V → ℤ) (v₀ : V) : Fin n → Finset V :=
  fun i => VarSup (F i) v₀




/-! ## Section 11: Overlap Information Content -/

/-- Total shared elements across all pairs. -/
def totalSharedElements {α : Type*} [DecidableEq α] {n : ℕ}
    (F : Fin n → Finset α) : ℕ :=
  ∑ p ∈ (univ ×ˢ univ).filter (fun p : Fin n × Fin n => p.1 < p.2),
    (F p.1 ∩ F p.2).card

/-
Zero shared elements for disjoint families.
-/

/-! ## Section 12: Conjecture -/



/-! ## Section 13: Overlap Deficit -/

/-- Total support size. -/
def totalSupportSz {α : Type*} [DecidableEq α] {n : ℕ}
    (F : Fin n → Finset α) : ℕ :=
  ∑ i : Fin n, (F i).card


