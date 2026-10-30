-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_completion_edge_count
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_completion_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:58:22.705621+00:00
-- url     : https://prove2.me/theorems/50d04fde-59ad-41f8-86bf-582c0a278416
-- title:
--   Maximal planar completion has the exact edge count
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices is contained in a drawable supergraph whose edge count is 3 times the number of vertices minus 6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_maximal_completion_edge_count {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
