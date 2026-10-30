-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_completion_30a2cd75
-- name    : WilliamsonShmoys.planar_drawing_has_triangulated_completion_30a2cd75
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T13:24:00.518071+00:00
-- url     : https://prove2.me/theorems/730ed87f-4857-4202-bf37-5fbad1be2596
-- title:
--   Every planar drawing has a spanning triangulation completion
-- statement:
--   Any drawable simple graph on a finite ordered vertex type with at least three vertices has a drawable supergraph on the same vertices whose edge count is exactly 3n−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_has_triangulated_completion_30a2cd75 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M) (hV : 3 ≤ Fintype.card V) : ∃ T : SimpleGraph V, M ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧ T.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
