-- Prove2me | solution 1 for HG.edgesSharingPair_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:46:36.266231+00:00
-- url     : https://prove2.me/submissions/4623b222-3757-457b-a422-110f3e8d32c2

-- Sol generated from Bridges/NeuralCoding/SubdIntegralityGap.lean
import Mathlib
import Definitions.Def_Bridges_NeuralCoding_SubdIntegralityGap
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


open HG

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Basic Definitions -/





/-! ## Pair Codegree -/





/-! ## Threshold Rounding -/



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


/-
In a d-uniform hypergraph with pair codegree ≤ K, the number of edges
    sharing a pair of vertices with `e` is at most K * C(d,2).

    Proof sketch: Edge `e` has d vertices, giving C(d,2) pairs. Each pair {u,v}
    appears in at most K edges other than `e` (by pair codegree bound).
    A different edge `e'` with |e ∩ e'| ≥ 2 must contain some pair from `e`.
    Summing over all C(d,2) pairs gives the bound.
-/

/-! ## Key Structural Lemma: Uncovered Edges Have Bounded Overlap -/


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


open HG in
theorem solution(H : HG V) (K d : ℕ)
    (hK : PairCodgrBounded H K)
    (hunif : IsUniform H d)
    (hd : 2 ≤ d)
    (e : Finset V) (he : e ∈ H.edges) :
    (edgesSharingPair H e).card ≤ K * d.choose 2 := by
  -- By definition of $edgesSharingPair$, we know that each edge in $edgesSharingPair e$ contains at least one pair of vertices from $e$.
  have h_edgesSharingPair_subset : H.edgesSharingPair e ⊆ Finset.biUnion (e.powerset.filter (fun s => s.card = 2)) (fun s => H.edges.filter (fun e' => s ⊆ e')) := by
    intro f hf; simp_all +decide [ Finset.subset_iff ] ;
    -- Since $f$ shares at least two vertices with $e$, we can choose any two such vertices and form a pair.
    obtain ⟨u, v, hu, hv, huv⟩ : ∃ u v : V, u ∈ e ∧ v ∈ e ∧ u ≠ v ∧ u ∈ f ∧ v ∈ f := by
      obtain ⟨ u, hu, v, hv, huv ⟩ := Finset.one_lt_card.1 ( Finset.mem_filter.mp hf |>.2.2 ) ; use u, v; aesop;
    exact ⟨ { u, v }, ⟨ by aesop_cat, by aesop_cat ⟩, Finset.mem_filter.mp hf |>.1, by aesop_cat ⟩;
  -- Each pair of vertices in $e$ is contained in at most $K$ edges.
  have h_pair_bound : ∀ s ∈ e.powerset.filter (fun s => s.card = 2), (H.edges.filter (fun e' => s ⊆ e')).card ≤ K := by
    intro s hs; rcases Finset.card_eq_two.mp ( Finset.mem_filter.mp hs |>.2 ) with ⟨ u, v, hu, hv, huv ⟩ ; simp_all +decide [ Finset.subset_iff ] ;
    exact hK u v hu;
  have h_card_filter : (e.powerset.filter (fun s => s.card = 2)).card ≤ Nat.choose d 2 := by
    simp +decide [ ← Finset.powersetCard_eq_filter, hunif e he ];
  exact le_trans ( Finset.card_le_card h_edgesSharingPair_subset ) ( le_trans ( Finset.card_biUnion_le ) ( by simpa [ mul_comm ] using Finset.sum_le_sum h_pair_bound |> le_trans <| by simpa [ mul_comm ] using Nat.mul_le_mul_left K h_card_filter ) )
