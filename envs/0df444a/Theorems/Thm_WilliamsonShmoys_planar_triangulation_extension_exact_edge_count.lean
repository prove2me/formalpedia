-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_exact_edge_count
-- name    : WilliamsonShmoys.planar_triangulation_extension_exact_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T09:57:30.471988+00:00
-- url     : https://prove2.me/theorems/74be3e12-14be-4de0-850b-748cf0e05d60
-- title:
--   Planar drawing extends to a triangulation with exact edge count
-- statement:
--   Every drawable graph on at least three vertices has a drawable supergraph on the same vertex type whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension_exact_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ J : SimpleGraph V,
      H <= J ∧
      WilliamsonShmoys.HasPlanarDrawingOn J ∧
      J.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
