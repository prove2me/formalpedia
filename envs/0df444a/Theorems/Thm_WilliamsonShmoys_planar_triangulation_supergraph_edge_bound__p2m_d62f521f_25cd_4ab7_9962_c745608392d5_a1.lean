-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_edge_bound__p2m_d62f521f_25cd_4ab7_9962_c745608392d5_a1
-- name    : WilliamsonShmoys.planar_triangulation_supergraph_edge_bound__p2m_d62f521f_25cd_4ab7_9962_c745608392d5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:48:42.247989+00:00
-- url     : https://prove2.me/theorems/ffbccb21-453c-4aae-b4fb-4ee36a71a8e5
-- title:
--   Planar augmentation to the maximal edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertices whose edge count is exactly three times the vertex count minus six, and whose edge count bounds the original graph’s edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_supergraph_edge_bound__p2m_d62f521f_25cd_4ab7_9962_c745608392d5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hDraw : HasPlanarDrawingOn N)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      N ≤ H ∧ HasPlanarDrawingOn H ∧
      N.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
