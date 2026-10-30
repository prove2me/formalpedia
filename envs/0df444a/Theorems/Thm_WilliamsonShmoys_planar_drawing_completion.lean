-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_completion
-- name    : WilliamsonShmoys.planar_drawing_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:43:49.765845+00:00
-- url     : https://prove2.me/theorems/7b0f0259-fdff-4f2f-8071-8a0ca08f5fc0
-- title:
--   Completion of a finite planar drawing to a triangulation
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
