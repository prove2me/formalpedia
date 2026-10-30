-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_2a72d934_5721_47e6_9f14_7bb2bf8ff8c2_a2
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_2a72d934_5721_47e6_9f14_7bb2bf8ff8c2_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T11:48:51.599642+00:00
-- url     : https://prove2.me/theorems/9a006411-f424-41be-bae2-b9a9d8f6aac6
-- title:
--   Exact edge count for a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on a finite ordered vertex type with at least three vertices has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_2a72d934_5721_47e6_9f14_7bb2bf8ff8c2_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      N.edgeSet ⊆ M.edgeSet) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
