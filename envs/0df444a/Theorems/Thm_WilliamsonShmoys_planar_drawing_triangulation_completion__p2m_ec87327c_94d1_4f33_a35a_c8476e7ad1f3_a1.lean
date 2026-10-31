-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion__p2m_ec87327c_94d1_4f33_a35a_c8476e7ad1f3_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_ec87327c_94d1_4f33_a35a_c8476e7ad1f3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:01:50.256496+00:00
-- url     : https://prove2.me/theorems/97ea1df5-d556-4f68-a658-dec2bacf773d
-- title:
--   Planar drawings admit a triangulated completion
-- statement:
--   Any drawable simple graph on at least three vertices has a drawable supergraph on the same vertex type whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_ec87327c_94d1_4f33_a35a_c8476e7ad1f3_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : HasPlanarDrawingOn H) (hCard : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧ K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
