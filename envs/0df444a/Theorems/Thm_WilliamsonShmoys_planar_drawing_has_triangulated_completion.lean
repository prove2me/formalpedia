-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_completion
-- name    : WilliamsonShmoys.planar_drawing_has_triangulated_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:00:13.333428+00:00
-- url     : https://prove2.me/theorems/e1f4fa2d-5048-4ecd-828e-2c1c603c9078
-- title:
--   Every finite planar drawing has a triangulated completion
-- statement:
--   Every finite simple graph with a crossing-free drawing on at least three vertices is contained, on the same vertex set, in a crossing-free triangulation with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_triangulated_completion {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDrawing : HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧ 3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry
