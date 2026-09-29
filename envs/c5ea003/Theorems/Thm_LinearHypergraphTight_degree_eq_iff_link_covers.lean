-- Prove2me | Theorems.Thm_LinearHypergraphTight_degree_eq_iff_link_covers
-- name    : LinearHypergraphTight.degree_eq_iff_link_covers
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:06:50.169249+00:00
-- url     : https://prove2.me/theorems/84baf63d-134a-4a51-bebf-68e7d1af5f16
-- title:
--   Degree eq iff link covers
-- statement:
--   Formal statement of `LinearHypergraphTight.degree_eq_iff_link_covers` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem LinearHypergraphTight.degree_eq_iff_link_covers{edges : Finset (Finset V)} {r : ℕ}
--       (huni : IsUniform edges r) (hlin : IsLinear edges) (v : V) :
--       degree edges v * (r - 1) = Fintype.card V - 1 ↔
--         ∀ w : V, w ≠ v → ∃ e ∈ edges, v ∈ e ∧ w ∈ e := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/LinearHypergraphConfigTightness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/LinearHypergraphConfigTightness.lean#L169

-- Thm stub generated from Novelty/LinearHypergraphConfigTightness.lean
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



/-
The disjoint union of per-edge pair-sets has exactly `m · C(r,2)` elements.
-/

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

theorem LinearHypergraphTight.degree_eq_iff_link_covers{edges : Finset (Finset V)} {r : ℕ}
    (huni : IsUniform edges r) (hlin : IsLinear edges) (v : V) :
    degree edges v * (r - 1) = Fintype.card V - 1 ↔
      ∀ w : V, w ≠ v → ∃ e ∈ edges, v ∈ e ∧ w ∈ e := by sorry
