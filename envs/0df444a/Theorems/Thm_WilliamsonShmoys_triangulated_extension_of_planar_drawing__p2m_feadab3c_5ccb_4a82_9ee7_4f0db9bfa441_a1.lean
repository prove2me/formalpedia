-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangulated_extension_of_planar_drawing__p2m_feadab3c_5ccb_4a82_9ee7_4f0db9bfa441_a1
-- name    : WilliamsonShmoys.triangulated_extension_of_planar_drawing__p2m_feadab3c_5ccb_4a82_9ee7_4f0db9bfa441_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:19:36.823424+00:00
-- url     : https://prove2.me/theorems/303ddd52-95e9-4125-a752-478be76ea7a5
-- title:
--   Triangulated drawable extension on the same vertex set
-- statement:
--   This child isolates the drawing-to-triangulation and planar-counting work. Starting from the given connected drawing with at least three vertices, extend it by drawable edges on the same vertex set until every face is triangular, then use Euler’s formula and edge-face incidences to obtain the exact edge count. The parent applies maximality to this extension, identifies T with U, and concludes by the child’s equality. The geometric construction and counting argument remain to be proved.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.triangulated_extension_of_planar_drawing__p2m_feadab3c_5ccb_4a82_9ee7_4f0db9bfa441_a1 {V : Type} [Fintype V] [LinearOrder V] (U : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hU : WilliamsonShmoys.HasPlanarDrawingOn U) (hconn : U.Connected) : ∃ T : SimpleGraph V, U ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧ T.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
