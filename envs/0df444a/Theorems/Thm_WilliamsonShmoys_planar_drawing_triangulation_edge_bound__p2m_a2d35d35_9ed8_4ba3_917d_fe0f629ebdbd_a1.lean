-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_edge_bound__p2m_a2d35d35_9ed8_4ba3_917d_fe0f629ebdbd_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_edge_bound__p2m_a2d35d35_9ed8_4ba3_917d_fe0f629ebdbd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:16:53.031587+00:00
-- url     : https://prove2.me/theorems/25a042c7-1a1b-47c9-a392-cae86f15b395
-- title:
--   Planar drawing extension to a triangulated edge bound
-- statement:
--   Every finite drawn simple planar graph on at least three vertices is contained, on the same vertex type, in a drawn planar graph with exactly 3|V|−6 edges. The original graph's edge count is no greater than the extension's.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_edge_bound__p2m_a2d35d35_9ed8_4ba3_917d_fe0f629ebdbd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
