-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_e8ae6a5a_5a4c_4f53_9707_6853e31c2747_a4
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_e8ae6a5a_5a4c_4f53_9707_6853e31c2747_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T00:55:13.776701+00:00
-- url     : https://prove2.me/theorems/07250582-440a-4fa1-86a2-9a1fddae4cd3
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices with no strictly larger drawable supergraph on the same vertex type has exactly three times the vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_e8ae6a5a_5a4c_4f53_9707_6853e31c2747_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hDraw : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
