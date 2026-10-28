-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_count_3v_minus_6
-- name    : WilliamsonShmoys.planar_supergraph_edge_count_3v_minus_6
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T02:25:33.266456+00:00
-- url     : https://prove2.me/theorems/2c7940e6-a778-4532-b0e6-040ffde52bce
-- title:
--   Drawable supergraph with the triangulation edge count
-- statement:
--   Every finite simple graph with at least three vertices and a crossing-free drawing is contained in a drawable graph on the same vertices whose edge count is 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_supergraph_edge_count_3v_minus_6
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
