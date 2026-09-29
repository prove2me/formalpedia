-- Prove2me | solution 1 for hitting_set_must_hit_sunflower_core
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:15:15.0791+00:00
-- url     : https://prove2.me/submissions/1ed7a6ec-e64d-4162-914c-7ba4d1317b92

-- Sol generated from Bridges/PosetTheory/SunflowerPruning.lean
import Mathlib
import Definitions.Def_Bridges_PosetTheory_SunflowerPruning

/-!
# Sunflower Pruning for Pythagorean Hypergraphs

This file develops the theory of sunflower-based search-tree pruning for
transversal (hitting set) computation on the Pythagorean triple hypergraph.

## Main Definitions

* `PythagoreanEdge` — Predicate for Pythagorean triple edges {a, b, c}
* `pythagoreanEdges n` — The 3-uniform hypergraph of Pythagorean triples in {1,…,n}
* `IsSunflowerOn` — Sunflower (Δ-system) with specified kernel
* `IsHittingSet` — Transversal / hitting set for a hypergraph
* `OverlapRich` — Vertex with high degree in hypergraph
* `vertexDegree` — Degree of a vertex in a hypergraph

## Main Results

* `incidence_sum_eq_uniformity_mul_edges` — Double-counting: ∑ deg(v) = r·|E| for r-uniform
* `exists_vertex_large_degree` — Averaging: some vertex has degree ≥ r·|E|/|V|
* `hitting_set_must_hit_sunflower_core` — Soundness of sunflower branching
* `bounded_hitting_set_forces_heavy_vertex` — Heavy vertices forced into small hitting sets

## Strategy

We follow Strategy A (incidence double-counting + sunflower forcing) combined with
Strategy C (kernelization-first algorithm proof). The key insight is that the
arithmetic structure of Pythagorean triples creates overlap-rich vertices that
sunflower extraction can exploit.

## References

* Erdős, R.; Rado, R. "Intersection theorems for systems of sets" (1960)
* Cygan et al. "Parameterized Algorithms" §7
* Heule, Kullmann, Marek "Solving the Boolean Pythagorean Triples Problem" (2016)
-/

open Finset

/-! ## Core Hypergraph Definitions -/








/-! ## Theorem 1: Incidence Double-Counting (Cross-Domain: Incidence Geometry) -/

/-
**Incidence identity for uniform hypergraphs.**
    For any hypergraph `H` on vertex set `V`, the sum of vertex degrees
    equals the sum of edge sizes. This is the fundamental double-counting
    identity connecting incidence geometry to hypergraph theory.

    Proof strategy: swap the order of summation using Finset.sum_comm.
-/

/-
**Corollary: For r-uniform hypergraphs, ∑ deg(v) = r · |E|.**
    When every edge has exactly `r` elements, the incidence sum simplifies.
-/

/-
**Averaging principle: existence of a high-degree vertex.**
    If the sum of degrees is at least `d * |V|`, then some vertex has
    degree at least `d`. This is the entry point for sunflower extraction.
-/

/-! ## Theorem 2: Sunflower Core Hitting (Algorithmic Correctness) -/

/-
**Sunflower core hitting theorem.**
    If `S` is a sunflower subfamily of `H` with core `c`, and `T` is a
    hitting set of `H` with `|T| ≤ k`, and `S` has more than `k` petals,
    then `T` must contain an element of the core `c`.

    This is the correctness theorem for sunflower-based branching:
    when we find a large sunflower, we can restrict branching to core elements.

    Proof: If T misses c entirely, then T must hit each edge of S in its
    petal (the part e \ c). Since petals are pairwise disjoint (by the
    sunflower property), T contains at least |S| distinct elements,
    contradicting |T| ≤ k < |S|.
-/

/-
**Bounded hitting set forces heavy vertex inclusion.**
    If vertex `v` has degree > k in hypergraph `H`, and the edges through `v`
    form a sunflower with core {v}, then every hitting set of size ≤ k must
    contain `v`.

    This is the arithmetic-combinatorial insight: heavy incidence around a
    vertex, combined with pairwise singleton intersection, creates forced
    transversal coordinates.
-/

/-! ## Theorem 3: Search Tree Domination -/



/-
**Sunflower branching dominates naive branching.**
    When the sunflower core has size s ≤ r, the pruned search explores
    at most as many nodes as the naive search.
    This is the monotonic domination theorem for the search tree.
-/

/-
**Strict improvement when core is smaller.**
    When the sunflower core is strictly smaller than edge size and k ≥ 1,
    the pruned search is strictly better.
-/

/-! ## Cross-Domain Connection: Parameterized Complexity -/

/-
A sunflower reduction step preserves hitting set existence:
    if we find a sunflower `S` with core `c` having > k petals,
    we can replace all of `S` with just `c` (as a single edge)
    without affecting whether a size-k hitting set exists.

    This is the FPT kernelization step.
-/

/-! ## Conjecture: Pruning Gain -/

/-
**Conjecture (Pythagorean Pruning Gain):**
   For the 3-uniform Pythagorean hypergraph on {1,…,n} with n ≥ 50,
   sunflower-based branching with singleton cores (s=1) reduces
   recursive calls by at least a factor of 3^k compared to naive (r=3) branching:

     recursiveCallsSunflower 1 k = 1 ≤ recursiveCallsNaive 3 k = 3^k

   This is trivially true by our definitions, but the non-trivial content is that
   singleton-core sunflowers actually exist in the Pythagorean hypergraph for
   moderate n — which our structural theorems guarantee via the high-degree
   vertex existence theorem.

The pruning gain from singleton-core sunflowers on 3-uniform hypergraphs
    is exponential in the budget parameter k.
-/

theorem solution    (H S : Finset (Finset ℕ)) (c T : Finset ℕ) (k : ℕ)
    (hSsub : S ⊆ H)
    (hSun : IsSunflowerOn S c)
    (hCard : k < S.card)
    (hHit : IsHittingSet T H)
    (hSize : T.card ≤ k) :
    (c ∩ T).Nonempty := by
  by_contra hCard; have := hSun.2; simp_all +decide [ IsHittingSet ] ;
  -- Since $c$ does not intersect $T$, for each $e \in S$, $T$ must contain at least one element from $e \setminus c$.
  have h_petals : ∀ e ∈ S, ∃ x ∈ T, x ∈ e \ c := by
    intro e he; specialize hHit e ( hSsub he ) ; obtain ⟨ x, hx ⟩ := hHit; use x; simp_all +decide [ Finset.ext_iff ] ;
    exact fun hx' => hCard x hx' hx.2;
  -- Since $T$ contains at least $|S|$ elements, one from each petal, and $|S| > k$, this contradicts $|T| \leq k$.
  have h_card_T : T.card ≥ S.card := by
    choose! f hf₁ hf₂ using h_petals;
    have h_card_T : Finset.card (Finset.image f S) ≥ S.card := by
      rw [ Finset.card_image_of_injOn ];
      intro e₁ he₁ e₂ he₂ h_eq; specialize this e₁ he₁ e₂ he₂; simp_all +decide [ Finset.ext_iff ] ;
      grind +ring;
    exact h_card_T.trans ( Finset.card_le_card <| Finset.image_subset_iff.mpr hf₁ );
  linarith
