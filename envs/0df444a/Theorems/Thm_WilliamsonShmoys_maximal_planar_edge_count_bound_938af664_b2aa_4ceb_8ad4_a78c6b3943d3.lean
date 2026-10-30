-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_bound_938af664_b2aa_4ceb_8ad4_a78c6b3943d3
-- name    : WilliamsonShmoys.maximal_planar_edge_count_bound_938af664_b2aa_4ceb_8ad4_a78c6b3943d3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T04:30:59.408217+00:00
-- url     : https://prove2.me/theorems/7be4c669-fb25-4ddf-9c54-927ee227fe8c
-- title:
--   Edge bound for maximal planar graphs
-- statement:
--   An inclusion-maximal graph admitting the specified crossing-free drawing has at most `3 * |V| - 6` edges when |V| ≥ 3. This is the topological core: maximality forces triangular faces, after which Euler’s formula gives the edge bound. The strict vertex-count hypothesis is retained, including the equality case |V| = 3.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_bound_938af664_b2aa_4ceb_8ad4_a78c6b3943d3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
