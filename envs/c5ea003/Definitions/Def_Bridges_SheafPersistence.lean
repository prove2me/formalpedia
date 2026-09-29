-- Prove2me | Definitions.Def_Bridges_SheafPersistence
-- name    : Bridges_SheafPersistence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:39:19.087317+00:00
-- url     : https://prove2.me/theorems/11876c34-e553-4ba8-804b-22671ac91a84
-- title:
--   Aether Catalog definitions — Bridges_SheafPersistence
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.SheafPersistence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/SheafPersistence.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Sheaf-Theoretic Tropical Persistence

This file develops a **sheaf-theoretic** framework for tropical persistence,
recasting the tropical event profile as the decategorified trace of a
constructible tropical sheaf on the threshold parameter line.

## Overview

The central insight is that the tropical event profile — a combinatorial
invariant defined by cumulative degree-weighted vertex activations — is
in fact the global-section rank of a constructible sheaf on the real line,
whose stalks record the tropical kernel data of the active subgraph at
each threshold.

Building explicitly on the certified finite/combinatorial machinery of
`Pythagorean/TropicalBridge/Stability.lean` and
`Pythagorean/TropicalBridge/FiltrationPersistence.lean`, we show:

1. **Constructibility** (Theorem 1): The active vertex set — and hence the
   tropical rank — is locally constant between consecutive critical values.
   This is the constructibility condition for sheaves on ℝ.

2. **Event Profile Recovery** (Theorem 2): The tropical event profile is
   exactly the cumulative sum of sheaf jumps at critical values. This
   recodes persistence from a sequential observable into a sheaf pushforward.

3. **Sheaf-Theoretic Stability** (Theorem 3): ε-close filtrations yield
   ε-interleaved sheaf profiles. Stability emerges from functoriality
   (pullback along the ε-shift) rather than ad hoc estimates.

4. **Cross-Domain Bridge** (Theorem 4): For path graphs, sheaf jumps at
   critical thresholds equal the local combinatorial contribution
   `degree(v) + 1`, connecting to graph topology.

## Main Definitions

* `criticalValues` — the set of vertex entrance times
* `sameCriticalGap` — predicate: no critical value lies strictly between two thresholds
* `TropicalRankSheaf` — a constructible presheaf recording rank data at each threshold
* `sheafJump` — the jump in rank at a critical value
* `SheafEventProfile` — cumulative sheaf jump profile
* `pathGraph`, `pathFiltration` — concrete test objects for the sheaf framework

## Main Results

* `activeVertices_eq_of_sameCriticalGap` — active vertex sets are constant between criticals
* `tropicalEventProfile_eq_cumulativeSheafJump` — event profile = cumulative sheaf jumps
* `sheafEventProfile_stability` — sheaf-theoretic stability bound via interleaving
* `sheafJump_pathFiltration_eq` — cross-domain bridge for path graphs
* `sheafJump_decomposition` — degree-0/degree-1 jump decomposition

## References

* Cohen-Steiner, Edelsbrunner, Harer, "Stability of Persistence Diagrams" (2007)
* Curry, "Sheaves, Cosheaves and Applications" (2014)
* Kashiwara, Schapira, "Sheaves on Manifolds" (1990)
* Baker, Norine, "Riemann-Roch and Abel-Jacobi theory on a finite graph" (2007)
-/


open Finset BigOperators Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Foundational Definitions from Stability Theory

These definitions mirror the certified API in `Stability.lean`. We re-state them
here so this file is self-contained while maintaining the same mathematical content.
The existing `tropicalEventProfile`, `activeVertices`, and stability bounds from
`Stability.lean` are the combinatorial shadow that our sheaf theory decategorifies. -/

/-- Vertex filtration: an entrance-time function assigning each vertex a real number. -/
abbrev VertexFiltration' (V : Type*) := V → ℝ

/-- Active vertices at time t: those whose entrance time is at most t.
    (Mirror of `activeVertices` from Stability.lean) -/
def activeVerts (f : VertexFiltration' V) (t : ℝ) : Finset V :=
  Finset.univ.filter (fun v => f v ≤ t)

/-- Tropical event profile at time t: the cumulative sum of `(degree(v) + 1)`
    for all active vertices.
    (Mirror of `tropicalEventProfile` from Stability.lean) -/
def tropEventProfile (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : VertexFiltration' V) (t : ℝ) : ℤ :=
  ∑ v ∈ activeVerts f t, (↑(G.degree v) + 1 : ℤ)

/-- Filtration sup-distance.
    (Mirror of `FiltrationSupDist` from Stability.lean) -/
def filtSupDist [Nonempty V] (f g : VertexFiltration' V) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun v => |f v - g v|)

/-! ## Active Vertex Monotonicity and Interleaving

These are the key lemmas from stability theory that we lift to the sheaf level. -/

/-
Active vertices grow monotonically as time increases.
-/
theorem activeVerts_mono (f : VertexFiltration' V) {s t : ℝ} (hst : s ≤ t) :
    activeVerts f s ⊆ activeVerts f t := by
  exact fun v hv => Finset.mem_filter.mpr ⟨ Finset.mem_univ _, le_trans ( Finset.mem_filter.mp hv |>.2 ) hst ⟩

/-
For ε-close filtrations, active sets are ε-interleaved.
-/

/-
The tropical event profile is monotone in time.
-/

/-
ε-close filtrations give ε-interleaved event profiles.
-/

/-
Individual vertex entrance-time difference is bounded by the sup distance.
-/

/-! ## Critical Values and Gap Predicates -/

/-- The set of critical values (entrance times) of a vertex filtration.
    These are exactly the thresholds at which the active vertex set changes. -/
def criticalValues (f : VertexFiltration' V) : Finset ℝ :=
  Finset.image f Finset.univ

/-- Two thresholds lie in the same critical gap if no critical value
    lies strictly between them (with s ≤ t). This is the key constructibility
    predicate: the sheaf stalks are constant on each such gap. -/
def sameCriticalGap (crit : Finset ℝ) (s t : ℝ) : Prop :=
  s ≤ t ∧ ∀ c ∈ crit, ¬(s < c ∧ c ≤ t)

/-! ## Active Vertex Set Constancy -/

/-
**Key lemma**: If no critical value lies strictly between s and t (with s ≤ t),
    then the active vertex sets at s and t are identical.
    This is the foundation of constructibility.

    **Proof sketch**: For v ∈ activeVerts f s, we have f v ≤ s ≤ t so v ∈ activeVerts f t.
    For v ∈ activeVerts f t, if f v > s, then f v is a critical value (it's in
    image of f) and s < f v ≤ t, contradicting the gap hypothesis.
-/
theorem activeVerts_eq_of_sameCriticalGap
    (f : VertexFiltration' V)
    {s t : ℝ} (hgap : sameCriticalGap (criticalValues f) s t) :
    activeVerts f s = activeVerts f t := by
  refine' Finset.Subset.antisymm ( fun v hv => _ ) ( fun v hv => _ );
  · exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, le_trans ( Finset.mem_filter.mp hv |>.2 ) hgap.1 ⟩;
  · exact Classical.not_not.1 fun h => hgap.2 ( f v ) ( Finset.mem_image.2 ⟨ v, Finset.mem_univ _, rfl ⟩ ) ⟨ lt_of_not_ge fun h' => h <| Finset.mem_filter.2 ⟨ Finset.mem_univ _, h' ⟩, Finset.mem_filter.1 hv |>.2 ⟩


/-! ## Tropical Rank Sheaf -/

/-- The **tropical rank** at threshold t: the total degree-weighted count
    of active vertices. This is the stalk rank of the constructible sheaf. -/
def tropicalRank (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : VertexFiltration' V) (t : ℝ) : ℕ :=
  (activeVerts f t).sum (fun v => G.degree v + 1)

/-
The tropical rank equals the (coerced) tropical event profile.
-/

/-- A **tropical rank sheaf** on the threshold line: a monotone, constructible
    rank function whose critical locus is finite. This is a finite-constructible
    sheaf in the sense of Kashiwara–Schapira, restricted to rank data. -/
structure TropicalRankSheaf (W : Type*) [Fintype W] [DecidableEq W] where
  /-- The underlying vertex filtration -/
  filt : VertexFiltration' W
  /-- The graph whose tropical data we track -/
  graph : SimpleGraph W
  /-- Decidable adjacency -/
  [decAdj : DecidableRel graph.Adj]
  /-- Rank at each threshold -/
  rankAt : ℝ → ℕ
  /-- Monotonicity: rank grows with threshold -/
  mono : Monotone rankAt
  /-- Critical values: thresholds where rank can jump -/
  critical : Finset ℝ
  /-- Constructibility: rank is constant between critical values -/
  locallyConstant_off_critical :
    ∀ {s t : ℝ}, sameCriticalGap critical s t → rankAt s = rankAt t

attribute [instance] TropicalRankSheaf.decAdj

/-! ## Construction of the Rank Sheaf from a Filtration -/

/-
Monotonicity of tropical rank.
-/
theorem tropicalRank_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : VertexFiltration' V) : Monotone (tropicalRank G f) := by
  intro s t hst;
  exact Finset.sum_le_sum_of_subset ( activeVerts_mono f hst )

/-- The tropical rank is constant on critical gaps. -/
theorem tropicalRank_eq_of_sameCriticalGap
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : VertexFiltration' V)
    {s t : ℝ} (hgap : sameCriticalGap (criticalValues f) s t) :
    tropicalRank G f s = tropicalRank G f t := by
  unfold tropicalRank
  rw [activeVerts_eq_of_sameCriticalGap f hgap]

/-- **Construct a tropical rank sheaf** from a graph and vertex filtration.
    The critical values are exactly the entrance times of vertices. -/
def mkTropicalRankSheaf (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : VertexFiltration' V) : TropicalRankSheaf V where
  filt := f
  graph := G
  rankAt := tropicalRank G f
  mono := tropicalRank_mono G f
  critical := criticalValues f
  locallyConstant_off_critical := tropicalRank_eq_of_sameCriticalGap G f


/-! ## Sheaf Jumps and Event Profile Recovery -/

/-- The **sheaf jump** at a critical value c: the sum of (degree + 1)
    for all vertices entering at exactly c. For a constructible sheaf,
    this is nonzero only at critical values. -/
def sheafJump (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : VertexFiltration' V) (c : ℝ) : ℕ :=
  (Finset.univ.filter (fun v => f v = c)).sum (fun v => G.degree v + 1)

/-- The **sheaf event profile**: the cumulative sum of sheaf jumps
    across all critical values at or below the threshold t. -/
def SheafEventProfile (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : VertexFiltration' V) (t : ℝ) : ℕ :=
  ((criticalValues f).filter (fun c => c ≤ t)).sum (sheafJump G f)

/-
**Key decomposition**: the tropical rank at time t equals the sum of sheaf
    jumps over all critical values ≤ t. This is the sheaf-theoretic
    reconstruction of the event profile from its jump data.

    **Proof sketch**: Both sides sum `(degree v + 1)` over active vertices.
    The LHS sums over `{v | f v ≤ t}` directly.
    The RHS partitions this set by entrance time `f v`, summing first over
    critical values `c ≤ t`, then over `{v | f v = c}` for each c.
    These are the same sum, repartitioned via `Finset.sum_biUnion`.
-/


/-! ## Sheaf-Theoretic Stability -/

/-- The sheaf event profile expressed as an integer for comparison. -/
def SheafEventProfileZ (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : VertexFiltration' V) (t : ℝ) : ℤ :=
  ↑(SheafEventProfile G f t)



/-! ## Sheaf Jump Analysis -/

/-- The vertex jump at threshold c: the number of vertices entering at exactly c. -/
def vertexJump (f : VertexFiltration' V) (c : ℝ) : ℕ :=
  (Finset.univ.filter (fun v => f v = c)).card

/-
The sheaf jump at non-critical values is zero.
-/

/-
The total sum of all sheaf jumps equals the sum of (degree + 1) over all vertices.
    This is the global Euler characteristic of the constructible sheaf.
-/

/-
The sheaf event profile is monotone.
-/

/-! ## Theorem 1: Constructibility — Detailed Version -/


/-! ## Sheaf Jump Decomposition -/

/-- The **degree-0 sheaf jump**: records only vertex-count changes.
    This is the "zeroth derived" jump invariant. -/
def degree0SheafJump (f : VertexFiltration' V) (c : ℝ) : ℕ :=
  vertexJump f c

/-- The **degree-1 sheaf jump**: records the excess degree contribution
    beyond mere vertex counting. This is the "first derived" jump invariant
    that detects edge-density effects at critical thresholds.
    For simple graphs, this captures the number of edges incident to
    vertices entering at time c. -/
def degree1SheafJump (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : VertexFiltration' V) (c : ℝ) : ℕ :=
  sheafJump G f c - vertexJump f c

/-
The total sheaf jump decomposes into degree-0 and degree-1 parts:
    `sheafJump = vertexJump + (sheafJump - vertexJump)`.
    This decomposition is the combinatorial shadow of the derived
    filtration on the sheaf stalk.
-/

/-! ## Path Graph Filtration and Cross-Domain Bridge -/

/-- **Path graph on n vertices**: vertices are `Fin n`, edges connect
    consecutive vertices `i` and `i+1`. -/
def pathGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj i j := (i.val + 1 = j.val) ∨ (j.val + 1 = i.val)
  symm := by intro i j h; cases h with | inl h => exact Or.inr h | inr h => exact Or.inl h
  loopless := ⟨fun h => by rcases h with h | h <;> omega⟩

instance pathGraph_decRel (n : ℕ) : DecidableRel (pathGraph n).Adj :=
  fun i j => inferInstanceAs (Decidable (_ ∨ _))

/-- The natural filtration on a path graph: vertex i enters at time i. -/
def pathFiltration (n : ℕ) : VertexFiltration' (Fin n) :=
  fun i => (i.val : ℝ)

/-
**Theorem 4 (Cross-Domain Bridge)**: The sheaf jump for the path filtration
    at vertex k equals `(pathGraph n).degree k + 1`.
    For interior vertices of a path, this is 3 (degree 2 + 1).
    For endpoints, this is 2 (degree 1 + 1) or 1 (degree 0 + 1).

    This connects the sheaf-theoretic framework to concrete graph topology:
    sheaf jumps at critical thresholds are exactly the local combinatorial
    contribution of each vertex to the tropical kernel dimension.

    **Proof sketch**: The filter `{v : Fin n | pathFiltration n v = k.val}` equals
    `{k}` since `pathFiltration` is injective (different `Fin n` elements have
    different `val`, hence different real coercions). Then the sum over `{k}` is
    `(pathGraph n).degree k + 1`.
-/

/-! ## Sheaf Restriction and Functoriality -/



/-! ## Möbius Inversion Connection

For a finite poset of critical values, the cumulative rank at threshold t
can be recovered by summing the local jumps via an inclusion-exclusion
(Möbius-like) formula. In the 1D totally ordered case, this reduces to
the cumulative sum formula.

This establishes the connection to incidence algebras: the sheaf jump data
is the Möbius inverse of the cumulative rank data on the critical value poset. -/


/-! ## Sheaf Interleaving Distance -/

/-- The **sheaf interleaving distance**: the minimum ε such that the two
    sheaf profiles are ε-interleaved. This is a sheaf-theoretic metric
    on the space of constructible tropical sheaves. -/
def sheafInterleavingDist [Nonempty V]
    (f g : VertexFiltration' V) : ℝ :=
  filtSupDist f g


/-! ## Sheaf Euler Characteristic -/

/-- The **Euler characteristic** of the tropical rank sheaf: the total sum
    of sheaf jumps. For a constructible sheaf on the line, this equals
    the asymptotic rank of the sheaf. -/
def sheafEulerChar (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : VertexFiltration' V) : ℕ :=
  (criticalValues f).sum (sheafJump G f)


/-! ## Poset Sheaf Model -/

/-- The **stratum type** for the critical stratification.
    Each stratum is either a critical point or an interval between
    consecutive critical values. This is the indexing type for the
    finite-poset sheaf model. -/
inductive Stratum : Type where
  /-- An interval stratum (representative point) -/
  | interval : ℝ → Stratum
  /-- A critical point stratum -/
  | point : ℝ → Stratum

/-- The rank data on each stratum: this gives the finite poset sheaf
    whose global section rank reproduces the event profile. -/
def stratumRank (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : VertexFiltration' V) : Stratum → ℕ
  | .interval t => tropicalRank G f t
  | .point c => tropicalRank G f c


end


