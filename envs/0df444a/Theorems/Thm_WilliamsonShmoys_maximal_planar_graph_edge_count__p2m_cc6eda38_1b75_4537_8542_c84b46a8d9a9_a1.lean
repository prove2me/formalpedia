-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_cc6eda38_1b75_4537_8542_c84b46a8d9a9_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_cc6eda38_1b75_4537_8542_c84b46a8d9a9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:48:47.748619+00:00
-- url     : https://prove2.me/theorems/fba5509b-7521-41eb-ae0d-1c68b4ac0c26
-- title:
--   A maximal planar drawing has the triangulation edge count
-- statement:
--   For at least three vertices, a drawable simple graph with no proper drawable supergraph on the same vertices has exactly `3 |V| - 6` edges. This isolates the topological edge-count result from the parent’s finite maximal-choice step. A proof route is to establish that maximality forces every face of the drawing to be triangular, then count vertices, edges, and faces with Euler’s formula. The three-vertex boundary case is the triangle with three edges; the hypothesis excludes smaller vertex sets, where the formula need not hold.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open scoped BigOperators

theorem WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_cc6eda38_1b75_4537_8542_c84b46a8d9a9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ L : SimpleGraph V, H ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
