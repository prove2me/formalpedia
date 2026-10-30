-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_has_triangulated_extension
-- name    : WilliamsonShmoys.planar_drawingOn_has_triangulated_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T10:37:52.259858+00:00
-- url     : https://prove2.me/theorems/caf19f82-e2b3-4305-a0b5-02bb16caf8c9
-- title:
--   Planar drawing extends to a triangulation
-- statement:
--   Every graph with a crossing-free drawing on a finite ordered vertex set of size at least three has a planar supergraph on that same vertex set with exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_has_triangulated_extension {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
