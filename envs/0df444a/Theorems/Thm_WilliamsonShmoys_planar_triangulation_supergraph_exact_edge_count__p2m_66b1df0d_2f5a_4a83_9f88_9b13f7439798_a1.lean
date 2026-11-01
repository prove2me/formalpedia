-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count__p2m_66b1df0d_2f5a_4a83_9f88_9b13f7439798_a1
-- name    : WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_66b1df0d_2f5a_4a83_9f88_9b13f7439798_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:43:31.050503+00:00
-- url     : https://prove2.me/theorems/05cc95b8-6993-44ac-b777-7a2cce137e12
-- title:
--   Triangulation completion with exact planar edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices can be augmented, on the same vertex type, to a drawable graph with exactly 3|V|−6 edges. This applies without a connectedness assumption, including to edgeless graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open scoped BigOperators

theorem WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_66b1df0d_2f5a_4a83_9f88_9b13f7439798_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
