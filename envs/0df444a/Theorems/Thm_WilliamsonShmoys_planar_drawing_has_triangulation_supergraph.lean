-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulation_supergraph
-- name    : WilliamsonShmoys.planar_drawing_has_triangulation_supergraph
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T08:00:23.981859+00:00
-- url     : https://prove2.me/theorems/85252b40-ee02-4664-960a-c8af730317d2
-- title:
--   A crossing-free drawing extends to a triangulated planar supergraph
-- statement:
--   A finite graph with at least three vertices and a crossing-free drawing extends, on the same vertices, to a graph with a crossing-free drawing, the sharp planar edge count, and a triangular plane face system.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_TriangularPlaneFaceSystem

theorem WilliamsonShmoys.planar_drawing_has_triangulation_supergraph
    {V : Type} [Fintype V] [LinearOrder V] [DecidableEq V]
    (H : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V ∧
      WilliamsonShmoys.HasTriangularPlaneFaceSystem K := by sorry
