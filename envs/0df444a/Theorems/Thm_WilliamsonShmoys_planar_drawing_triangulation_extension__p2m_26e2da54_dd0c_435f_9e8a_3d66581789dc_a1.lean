-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_26e2da54_dd0c_435f_9e8a_3d66581789dc_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_26e2da54_dd0c_435f_9e8a_3d66581789dc_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:29:54.042556+00:00
-- url     : https://prove2.me/theorems/65576344-96ee-4070-89ba-6bada339cc97
-- title:
--   Triangulation extension of a planar drawing
-- statement:
--   A graph with a crossing-free drawing and at least three vertices extends on the same vertex set to a triangulated planar graph. The extension contains every original edge, so its edge count is at least the original count, and its edge count plus six equals three times the number of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_26e2da54_dd0c_435f_9e8a_3d66581789dc_a1 {V : Type} [Fintype V] [LinearOrder V] (Y : SimpleGraph V) (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) (hV : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, (∀ u v, Y.Adj u v → H.Adj u v) ∧ Y.edgeSet.ncard ≤ H.edgeSet.ncard ∧ H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
