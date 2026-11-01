-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_with_triangulated_edge_count__p2m_ff88384e_13a7_4e55_8777_790088f23a4a_a2
-- name    : WilliamsonShmoys.exists_planar_supergraph_with_triangulated_edge_count__p2m_ff88384e_13a7_4e55_8777_790088f23a4a_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:36:18.241768+00:00
-- url     : https://prove2.me/theorems/4c675a48-b2e7-41d9-8987-0c6f38bd3a34
-- title:
--   Drawable supergraph with triangulated edge count
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertices with exactly 3|V| − 6 edges. This packages extending the drawing to a triangulation and applying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_supergraph_with_triangulated_edge_count__p2m_ff88384e_13a7_4e55_8777_790088f23a4a_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
