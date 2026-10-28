-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulation_completion
-- name    : WilliamsonShmoys.planar_drawing_has_triangulation_completion
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T14:44:59.721508+00:00
-- url     : https://prove2.me/theorems/e51c1790-43b6-44f6-8bd2-7250952eeba7
-- title:
--   Planar drawing admits a triangulated completion
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices has a drawable supergraph on the same vertex set whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_has_triangulation_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V,
      T ≤ U ∧
      WilliamsonShmoys.HasPlanarDrawingOn U ∧
      3 * Fintype.card V = U.edgeSet.ncard + 6 := by sorry
