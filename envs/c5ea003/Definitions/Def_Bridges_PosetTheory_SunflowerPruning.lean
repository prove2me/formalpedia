-- Prove2me | Definitions.Def_Bridges_PosetTheory_SunflowerPruning
-- name    : Bridges_PosetTheory_SunflowerPruning
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:32:44.982133+00:00
-- url     : https://prove2.me/theorems/96a06fd1-55ed-4f72-9ed5-f42b0a4f7a5c
-- title:
--   Aether Catalog definitions — Bridges_PosetTheory_SunflowerPruning
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PosetTheory.SunflowerPruning`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PosetTheory/SunflowerPruning.lean by skeleton subtraction
import Mathlib

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

/-- The degree of vertex `v` in hypergraph `H`: number of edges containing `v`. -/
def vertexDegree (H : Finset (Finset ℕ)) (v : ℕ) : ℕ :=
  (H.filter fun e => v ∈ e).card

/-- A set `T` is a hitting set (transversal) of hypergraph `H` if `T`
    intersects every edge. -/
def IsHittingSet (T : Finset ℕ) (H : Finset (Finset ℕ)) : Prop :=
  ∀ e ∈ H, (e ∩ T).Nonempty

/-- A family `S` of sets is a sunflower with kernel `c` if `c ⊆ e` for all
    `e ∈ S` and distinct members intersect exactly in `c`. -/
def IsSunflowerOn (S : Finset (Finset ℕ)) (c : Finset ℕ) : Prop :=
  (∀ e ∈ S, c ⊆ e) ∧
  (∀ e₁ ∈ S, ∀ e₂ ∈ S, e₁ ≠ e₂ → e₁ ∩ e₂ = c)


/-- The Pythagorean edge predicate: {a,b,c} is a Pythagorean triple with
    a < b < c and a² + b² = c², all in {1,…,n}. -/
def IsPythagoreanEdge (n a b c : ℕ) : Prop :=
  1 ≤ a ∧ a < b ∧ b < c ∧ c ≤ n ∧ a ^ 2 + b ^ 2 = c ^ 2

instance (n a b c : ℕ) : Decidable (IsPythagoreanEdge n a b c) := by
  unfold IsPythagoreanEdge; infer_instance


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

/-- Naive branching recursive call count: branch on each element of an
    uncovered edge, giving branching factor equal to edge size.
    For a k-bounded hitting set search on r-uniform hypergraph with m edges,
    naive branching gives at most r^k calls (each step picks one of r elements
    and decreases budget by 1). -/
def recursiveCallsNaive (r k : ℕ) : ℕ := r ^ k

/-- Sunflower-pruned branching: when a sunflower with core of size `s` is found,
    branch only on core elements (branching factor s instead of r).
    For 3-uniform hypergraphs (r=3) with singleton cores (s=1), this
    gives 1^k = 1 branching in the pruned steps, versus 3^k naive.
    In the worst case (no sunflower found), we fall back to naive branching.
    We model the best case: sunflower core size ≤ r, giving s^k ≤ r^k. -/
def recursiveCallsSunflower (s k : ℕ) : ℕ := s ^ k

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


