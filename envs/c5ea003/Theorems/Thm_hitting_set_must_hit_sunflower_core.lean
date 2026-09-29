-- Prove2me | Theorems.Thm_hitting_set_must_hit_sunflower_core
-- name    : hitting_set_must_hit_sunflower_core
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:33:34.464332+00:00
-- url     : https://prove2.me/theorems/38a3efd6-3ffe-4c47-8640-5e1088fa110a
-- title:
--   Hitting set must hit sunflower core
-- statement:
--   Formal statement of `hitting_set_must_hit_sunflower_core` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem hitting_set_must_hit_sunflower_core    (H S : Finset (Finset ℕ)) (c T : Finset ℕ) (k : ℕ)
--       (hSsub : S ⊆ H)
--       (hSun : IsSunflowerOn S c)
--       (hCard : k < S.card)
--       (hHit : IsHittingSet T H)
--       (hSize : T.card ≤ k) :
--       (c ∩ T).Nonempty := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/PosetTheory/SunflowerPruning.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/PosetTheory/SunflowerPruning.lean#L137

-- Thm stub generated from Bridges/PosetTheory/SunflowerPruning.lean
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

theorem hitting_set_must_hit_sunflower_core    (H S : Finset (Finset ℕ)) (c T : Finset ℕ) (k : ℕ)
    (hSsub : S ⊆ H)
    (hSun : IsSunflowerOn S c)
    (hCard : k < S.card)
    (hHit : IsHittingSet T H)
    (hSize : T.card ≤ k) :
    (c ∩ T).Nonempty := by sorry
