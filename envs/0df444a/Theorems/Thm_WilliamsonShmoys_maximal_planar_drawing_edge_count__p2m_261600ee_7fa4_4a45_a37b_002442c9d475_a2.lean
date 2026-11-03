-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_261600ee_7fa4_4a45_a37b_002442c9d475_a2
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_261600ee_7fa4_4a45_a37b_002442c9d475_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:05:16.804512+00:00
-- url     : https://prove2.me/theorems/e592f479-7758-40c0-97f7-ee5e29c0fee3
-- title:
--   An inclusion-maximal planar drawing has the sharp edge count
-- statement:
--   A drawable graph maximal among drawable supergraphs on the same vertex set, with at least three vertices, has exactly 3|V|−6 edges. This removes the Euler-counting step from the parent. A proof route is to formalize that maximality forces a connected triangulation for the given crossing-free arc drawing, then combine Euler’s formula with the fact that each edge is incident to two triangular face sides. The lower bound on the vertex count is necessary for this edge-count formula; in particular, the three-vertex maximal graph has three edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_261600ee_7fa4_4a45_a37b_002442c9d475_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
