-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_edge_count__p2m_d4833247_a107_430f_bfde_1b2cd697853a_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension_edge_count__p2m_d4833247_a107_430f_bfde_1b2cd697853a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:25:11.117983+00:00
-- url     : https://prove2.me/theorems/2f30e2d9-4845-4c04-a5c2-ea4608bfb1b9
-- title:
--   Planar triangulation extension edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex type whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_extension_edge_count__p2m_d4833247_a107_430f_bfde_1b2cd697853a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ T : SimpleGraph V,
      Set.Subset H.edgeSet T.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      T.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
