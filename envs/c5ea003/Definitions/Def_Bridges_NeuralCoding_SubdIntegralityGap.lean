-- Prove2me | Definitions.Def_Bridges_NeuralCoding_SubdIntegralityGap
-- name    : Bridges_NeuralCoding_SubdIntegralityGap
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:30:28.310884+00:00
-- url     : https://prove2.me/theorems/fcf0d5bf-8217-4307-896e-125d3e7d112c
-- title:
--   Aether Catalog definitions — Bridges_NeuralCoding_SubdIntegralityGap
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.NeuralCoding.SubdIntegralityGap`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/NeuralCoding/SubdIntegralityGap.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2024 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Sub-d Integrality Gap from Bounded Pair Codegree

This file develops the theory of pair codegree in hypergraphs and proves
structural results towards the strict sub-d integrality gap conjecture:
for d-uniform hypergraphs with bounded pair codegree, the ratio τ/τ* is
strictly less than d.

## Main Definitions

* `HG` — a hypergraph on vertex type `V`, given by a finite set of edges
* `HG.pairCodgr` — the codegree of a pair of vertices
* `HG.PairCodgrBounded` — predicate that pair codegree is bounded by K
* `HG.IsUniform` — predicate that all edges have the same cardinality
* `HG.IsTransversal` — a finset hitting every edge
* `HG.IsFracTransversal` — a fractional transversal (LP relaxation feasible point)
* `HG.thresholdSet` — the threshold rounding operator

## Main Results

* `HG.pairCodgr_comm` — pair codegree is symmetric
* `HG.thresholdSet_isTransversal` — threshold set at 1/d is a transversal for d-uniform H
* `HG.thresholdSet_card_bound` — |threshold set| ≤ d · τ*
* `HG.uncovered_edge_overlap_bound` — bounded pair codegree limits shared-pair neighbors
* `HG.uniform_transversal_exists` — existence of a transversal of size ≤ d · τ*

## References

* Lovász, "On the ratio of optimal integral and fractional covers" (1975)
* Aharoni, Holzman, Krivelevich, "On a theorem of Lovász" (1996)
-/

open Finset BigOperators

/-! ## Hypergraph Definition -/

/-- A hypergraph on vertex type `V` is a finite collection of edges,
    where each edge is a finset of vertices. -/
structure HG (V : Type*) where
  edges : Finset (Finset V)

namespace HG

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Basic Definitions -/

/-- A hypergraph is k-uniform if all edges have exactly k elements. -/
def IsUniform (H : HG V) (k : ℕ) : Prop :=
  ∀ e ∈ H.edges, e.card = k

/-- A finset `S` is a transversal of `H` if it intersects every edge. -/
def IsTransversal (H : HG V) (S : Finset V) : Prop :=
  ∀ e ∈ H.edges, (S ∩ e).Nonempty

/-- A function `x : V → ℝ` is a fractional transversal if it is nonneg
    and sums to ≥ 1 on every edge. -/
def IsFracTransversal (H : HG V) (x : V → ℝ) : Prop :=
  (∀ v, 0 ≤ x v) ∧ ∀ e ∈ H.edges, 1 ≤ ∑ v ∈ e, x v

/-- Total weight of a fractional assignment. -/
noncomputable def fracValue (x : V → ℝ) : ℝ :=
  ∑ v : V, x v

/-! ## Pair Codegree -/

/-- The pair codegree of vertices `u, v` in `H`: the number of edges containing both. -/
def pairCodgr (H : HG V) (u v : V) : ℕ :=
  (H.edges.filter (fun e => u ∈ e ∧ v ∈ e)).card

/-- The pair codegree is bounded by `K` if every distinct pair appears in ≤ K edges. -/
def PairCodgrBounded (H : HG V) (K : ℕ) : Prop :=
  ∀ u v : V, u ≠ v → H.pairCodgr u v ≤ K



/-! ## Threshold Rounding -/

/-- The threshold set: vertices with weight at least θ. -/
noncomputable def thresholdSet (x : V → ℝ) (θ : ℝ) : Finset V :=
  Finset.univ.filter (fun v => θ ≤ x v)


/-
For a d-uniform hypergraph with d ≥ 1, if x is a fractional transversal,
    then every edge has some vertex with x(v) ≥ 1/d.
-/

/-
The threshold set at level 1/d is a transversal for d-uniform hypergraphs.
-/

/-
The threshold set has cardinality at most d times the fractional value.
-/


/-! ## Overlap Structure from Pair Codegree -/

/-- The set of edges sharing a pair with a given edge `e`. -/
def edgesSharingPair (H : HG V) (e : Finset V) : Finset (Finset V) :=
  H.edges.filter (fun e' => e' ≠ e ∧ 2 ≤ (e ∩ e').card)

/-
In a d-uniform hypergraph with pair codegree ≤ K, the number of edges
    sharing a pair of vertices with `e` is at most K * C(d,2).

    Proof sketch: Edge `e` has d vertices, giving C(d,2) pairs. Each pair {u,v}
    appears in at most K edges other than `e` (by pair codegree bound).
    A different edge `e'` with |e ∩ e'| ≥ 2 must contain some pair from `e`.
    Summing over all C(d,2) pairs gives the bound.
-/

/-! ## Key Structural Lemma: Uncovered Edges Have Bounded Overlap -/

/-- The uncovered edges: edges not hit by a vertex set S. -/
def uncoveredEdges (H : HG V) (S : Finset V) : Finset (Finset V) :=
  H.edges.filter (fun e => Disjoint S e)

/-
Uncovered edges in a d-uniform hypergraph with pair codegree ≤ K:
    each uncovered edge shares a pair with at most K * C(d,2) other uncovered edges.
    This is a monotonicity consequence of the global bound.
-/

/-! ## The Greedy Coloring Bound -/

/-
If a finite set of items has the property that each item has at most Δ
"neighbors", then the items can be colored with at most Δ + 1 colors
such that no two neighbors share a color.
(This is the greedy coloring bound for graphs of max degree Δ.)

Here we state a consequence: the items can be partitioned into at most
Δ + 1 independent sets.

**Greedy coloring bound**: A graph on a finset of vertices with max degree Δ
    admits a proper (Δ+1)-coloring. This is the standard greedy coloring theorem.
    The coloring function is total on α; the proper coloring property is
    restricted to vertices in `items`.
-/

/-! ## Independent Set Cover Bound -/

/-
In a collection of d-element sets where any two share at most 1 element,
    we can find a transversal by picking one element from each set.
    The minimum number of elements needed to hit all sets is at most
    the number of sets (trivially), but also at most ⌈n/d⌉ where
    n = total number of elements involved, by a greedy argument.

    This is the key "repair" step: an independent set in the conflict graph
    consists of edges pairwise sharing at most 1 vertex, and can be
    covered efficiently.
-/

/-! ## Combined Bound: Sub-d Gap for Bounded Pair Codegree -/


/-! ## Pair Codegree Monotonicity Under Subhypergraph -/

/-
Pair codegree is monotone under taking subhypergraphs.
-/


/-! ## Pair Codegree and Edge Count -/

/-
The number of edges in a d-uniform hypergraph with n vertices and pair codegree ≤ K
    is at most K · C(n,2) / C(d,2). This is a basic double-counting bound.

    Proof: Count pairs (pair, edge) where pair ⊆ edge.
    Each edge contributes C(d,2) pairs. Each pair appears in ≤ K edges.
    So |E| · C(d,2) ≤ K · C(n,2), giving |E| ≤ K · C(n,2) / C(d,2).
-/

end HG


