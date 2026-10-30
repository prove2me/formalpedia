-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_triangulation_completion_aa4e0804
-- name    : WilliamsonShmoys.planar_edge_count_triangulation_completion_aa4e0804
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:32:05.141169+00:00
-- url     : https://prove2.me/theorems/e89e6305-81d9-40b6-95c3-e18b39e65d99
-- title:
--   Planar triangulation completion and edge count
-- statement:
--   Every simply planar graph on a fixed finite vertex set of at least three vertices is contained in a simply planar graph on that same vertex set whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_triangulation_completion_aa4e0804
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    Exists fun H : SimpleGraph V =>
      G <= H /\ WilliamsonShmoys.HasPlanarDrawingOn H /\
        H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
