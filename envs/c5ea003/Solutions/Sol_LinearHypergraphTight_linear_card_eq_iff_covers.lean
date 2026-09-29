-- Prove2me | solution 1 for LinearHypergraphTight.linear_card_eq_iff_covers
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:36:25.809103+00:00
-- url     : https://prove2.me/submissions/4aa7e731-cd79-49b8-8bc8-a7e456a7948b

-- Sol generated from Novelty/LinearHypergraphConfigTightness.lean
import Mathlib
import Definitions.Def_Novelty_LinearHypergraphConfigTightness
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Exact tightness of the density threshold for linear `r`-uniform hypergraphs

`Catalog/Novelty/LinearHypergraphDensityThreshold.lean` proved the global packing bound
`m · C(r,2) ≤ C(n,2)` for any linear `r`-uniform hypergraph and showed that a Steiner system
*attains* it (`steiner_card_eq`).  That gives one direction of optimality: a configuration meeting
the threshold exists.  This file pins down **exactly which configurations are tight**, sharpening
the catalog's optimality statement from an existence result to a complete characterization.

## Main results
* `linear_card_eq_iff_covers` — **global tightness characterization.**  For a linear `r`-uniform
  hypergraph, the packing bound is an *equality* `m · C(r,2) = C(n,2)` **iff** the hypergraph
  covers every pair of vertices (i.e. it is a Steiner system `S(2,r,n)`).  This upgrades
  `steiner_card_eq` (Steiner ⇒ equality) to a biconditional.
* `degree_mul_le` — **local packing bound.**  Each vertex `v` lies in at most `(n-1)/(r-1)` edges:
  `deg(v) · (r-1) ≤ n-1`.  This is the per-vertex ("link") refinement of the global bound.
* `degree_eq_iff_link_covers` — **local tightness characterization.**  Equality
  `deg(v) · (r-1) = n-1` holds **iff** the edges through `v` cover every other vertex.
* `covering_is_regular` — **Corollary.**  In a covering (Steiner) linear `r`-uniform hypergraph
  every vertex has the *same* degree, with `deg(v) · (r-1) = n-1`: tightness is global *and* local
  simultaneously, so Steiner systems are exactly the configurations that are tight everywhere.

## Catalog connections
* Extends `LinearHypergraph.linear_card_le` / `steiner_card_eq` (global bound + Steiner equality).
* The `e = 2` boundary of the Brown–Erdős–Sós extremal function (cf.
  `Catalog/Novelty/Catalog.Novelty.LinearBrownErdosSos.lean`): "every pair covered exactly once".

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the packing bound `m·C(r,2) ≤ C(n,2)` is proved by injecting the
  pairwise-disjoint per-edge pair-sets into the set of all `C(n,2)` pairs.  An injection of finite
  sets is onto iff the cardinalities match, so equality should be *equivalent* to surjectivity,
  i.e. every pair is covered — a Steiner system.  The same skeleton, applied vertex-locally to the
  link `{e : v ∈ e}` (whose erased edges `e \ {v}` are pairwise disjoint subsets of `V \ {v}`),
  should give the degree bound `deg(v)·(r-1) ≤ n-1` with the analogous tightness criterion.
Experiment (Experimenter): reused the `pairs_disjoint`/`biUnion_pairs_subset` engine from the
  catalog density file.  Global: `card_biUnion` turns `m·C(r,2)` into `|⋃ pair-sets|`; the bound
  is `⊆ univ.powersetCard 2`; equality of cardinalities of a `⊆` pair forces set equality
  (`Finset.eq_of_subset_of_card_le`), which decodes as full pair coverage.  Local: map
  `e ↦ e.erase v` over the link; linearity (`e₁ ∩ e₂ ⊆ {v}`) makes these disjoint, union `⊆`
  `univ.erase v` of size `n-1`.
Analysis (Analyst): the load-bearing fact in both directions is "disjoint ⊆ family is onto iff
  cardinalities agree".  No new geometry is needed beyond linearity = pair-disjointness; the
  characterizations are pure double-counting equalities.  The Fano plane `S(2,3,7)` is the smallest
  witness: `7·3 = 21 = C(7,2)` and `deg·(r-1) = 3·2 = 6 = n-1`, simultaneously tight.
Critique (Critic): none of the statements is vacuous.  `linear_card_eq_iff_covers` has content in
  both directions (⇐ is the catalog's `steiner_card_eq`; ⇒ is new).  `degree_mul_le` holds for
  every vertex including isolated ones (`deg = 0`).  `covering_is_regular` is a genuine equality,
  not an inequality, and is non-trivially satisfiable (Steiner systems exist, e.g. Fano).
Synthesis (PI): the density threshold for linear hypergraphs is tight *exactly* on Steiner systems,
  globally and locally.  This turns the catalog's one-sided optimality into an if-and-only-if and
  exhibits the extremal family explicitly, isolating the `e=2` Brown–Erdős–Sós boundary completely.
-- !-- Lab Notes -- !--
-/

open Finset

open LinearHypergraphTight

variable {V : Type*} [Fintype V] [DecidableEq V]





/-! ### The pair-disjointness engine (global) -/

omit [Fintype V] in
/-- For a linear family, the per-edge pair-sets `powersetCard 2 e` are pairwise disjoint. -/
theorem pairs_disjoint {edges : Finset (Finset V)} (hlin : IsLinear edges) :
    (edges : Set (Finset V)).PairwiseDisjoint (fun e => powersetCard 2 e) := by
  intro e he f hf hne
  by_contra h_inter
  have h_card : (e ∩ f).card ≥ 2 := by
    obtain ⟨p, hp₁, hp₂⟩ := Finset.not_disjoint_iff.mp h_inter
    exact Finset.card_le_card (Finset.subset_inter (Finset.mem_powersetCard.mp hp₁ |>.1)
      (Finset.mem_powersetCard.mp hp₂ |>.1)) |> le_trans (Finset.mem_powersetCard.mp hp₁ |>.2.ge)
  linarith [hlin e he f hf hne]


/-
The disjoint union of per-edge pair-sets has exactly `m · C(r,2)` elements.
-/
omit [Fintype V] in
theorem card_biUnion_pairs {edges : Finset (Finset V)} {r : ℕ}
    (huni : IsUniform edges r) (hlin : IsLinear edges) :
    (edges.biUnion (fun e => powersetCard 2 e)).card = edges.card * r.choose 2 := by
  rw [ Finset.card_biUnion ];
  · rw [ Finset.sum_congr rfl fun x hx => by rw [ Finset.card_powersetCard, huni x hx ] ] ; simp +decide;
  · convert pairs_disjoint hlin

/-! ### Global tightness characterization -/

/-
**Global tightness.** For a linear `r`-uniform hypergraph the packing bound is an equality
`m · C(r,2) = C(n,2)` if and only if every pair of vertices is covered (i.e. it is a Steiner
system).  The `⇐` direction recovers the catalog's `steiner_card_eq`; the `⇒` direction is the new
content, showing Steiner systems are the *only* tight configurations.
-/

/-! ### Local (degree) packing bound and its tightness -/

/-
The erased edges `e \ {v}` of the edges through `v` are pairwise disjoint (linearity).
-/

/-
**Local packing bound.** Each vertex lies in at most `(n-1)/(r-1)` edges:
`deg(v) · (r-1) ≤ n - 1`.
-/

/-
**Local tightness.** Equality in the degree bound, `deg(v) · (r-1) = n - 1`, holds iff the
edges through `v` cover every other vertex `w ≠ v`.
-/

/-
**Corollary: covering linear hypergraphs are regular.**  In a Steiner system every vertex has
the same degree, namely the one saturating the local bound `deg(v) · (r-1) = n - 1`.  Tightness is
therefore simultaneously global (`linear_card_eq_iff_covers`) and local at every vertex.
-/

/-! ### Cycle 2 — the handshake identity and a degree-theoretic edge count -/

/-
-- !-- Lab Notes -- !--
Hypothesis (Cycle 2): the global edge count of a Steiner system should be *re-derivable* purely
  from local regularity by double counting incidences.  The handshake identity
  `∑_v deg(v) = ∑_{e} |e|` (independent of linearity) specialises, for a uniform family, to
  `∑_v deg(v) = m·r`.  Summing the local regularity equality `deg(v)·(r-1) = n-1` over all `n`
  vertices then gives `m·r·(r-1) = n·(n-1)`, an alternative to the pair-count derivation of
  `steiner_card_eq` that flows through degrees rather than pairs.
Experiment/Analysis: `sum_degree_eq` is a pure Fubini swap of the incidence bipartite relation
  (`∑_v |{e : v∈e}| = ∑_e |{v : v∈e}| = ∑_e |e|`) with no structural hypotheses.
  `covering_edge_count` combines `sum_degree_eq` (uniform form `= m·r`) with `covering_is_regular`
  summed over `univ`.
Critique: `covering_edge_count` is the integer form `m·r·(r-1) = n·(n-1)`; for `r ≥ 2` it divides
  to the familiar `m = n(n-1)/(r(r-1))`.  It is not vacuous (Fano: `7·3·2 = 42 = 7·6`).
-- !-- Lab Notes -- !--

**Handshake identity.** The sum of vertex degrees equals the sum of edge sizes (incidence
double count); no linearity or uniformity needed.
-/

/-
For a `r`-uniform family the degree sum is exactly `m · r`.
-/

/-
**Degree-theoretic edge count.** A covering (Steiner) linear `r`-uniform hypergraph satisfies
`m · r · (r-1) = n · (n-1)`.  Derived by summing the local regularity identity
`covering_is_regular` over all vertices and using the handshake identity — a degrees-first route to
the Steiner edge count, complementing the pairs-first `linear_card_eq_iff_covers`.
-/


open LinearHypergraphTight in
theorem solution{edges : Finset (Finset V)} {r : ℕ}
    (huni : IsUniform edges r) (hlin : IsLinear edges) :
    edges.card * r.choose 2 = (Fintype.card V).choose 2 ↔ Covers edges := by
  have h_card : (edges.biUnion (fun e => powersetCard 2 e)).card = edges.card * r.choose 2 := by
    convert card_biUnion_pairs huni hlin
  have h_subset : edges.biUnion (fun e => powersetCard 2 e) ⊆ (Finset.powersetCard 2 (Finset.univ : Finset V)) := by
    grind +qlia
  have h_card_eq : (Finset.powersetCard 2 (Finset.univ : Finset V)).card = (Fintype.card V).choose 2 := by
    rw [ Finset.card_powersetCard, Finset.card_univ ]
  have h_iff_card : edges.card * r.choose 2 = (Fintype.card V).choose 2 ↔ (edges.biUnion (fun e => powersetCard 2 e)) = (Finset.powersetCard 2 (Finset.univ : Finset V)) := by
    exact ⟨ fun h => Finset.eq_of_subset_of_card_le h_subset ( by aesop ), fun h => by rw [ ← h_card, h, h_card_eq ] ⟩
  have h_iff_covers : (edges.biUnion (fun e => powersetCard 2 e)) = (Finset.powersetCard 2 (Finset.univ : Finset V)) ↔ Covers edges := by
    simp +decide [ Finset.ext_iff, Covers ];
    grind
  exact Iff.trans h_iff_card h_iff_covers
