-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_extends_to_triangulation
-- name    : WilliamsonShmoys.planar_drawing_extends_to_triangulation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T19:55:54.090992+00:00
-- url     : https://prove2.me/theorems/2b1bd58b-4118-4d94-af42-fe856e4e67a5
-- title:
--   Extending a drawable graph to a triangulation
-- statement:
--   Any drawable simple graph on a finite ordered vertex type with at least three vertices is a subgraph of a drawable graph on the same vertices having exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_extends_to_triangulation
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hQdraw : WilliamsonShmoys.HasPlanarDrawingOn Q) :
    ∃ R : SimpleGraph V,
      Q ≤ R ∧ WilliamsonShmoys.HasPlanarDrawingOn R ∧
        R.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
