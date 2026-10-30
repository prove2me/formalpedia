-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion_fixed_vertices_e7f6fb70
-- name    : WilliamsonShmoys.planar_triangulation_completion_fixed_vertices_e7f6fb70
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T17:20:58.059516+00:00
-- url     : https://prove2.me/theorems/f754e7f5-0138-4471-840c-fa82fd2ddf11
-- title:
--   Triangulation edge count completion on a fixed vertex type
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices has a drawable supergraph on the same vertex type whose edge count is three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_completion_fixed_vertices_e7f6fb70
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hX : WilliamsonShmoys.HasPlanarDrawingOn X) :
    ∃ Y : SimpleGraph V,
      X ≤ Y ∧ WilliamsonShmoys.HasPlanarDrawingOn Y ∧
      3 * Fintype.card V = Y.edgeSet.ncard + 6 := by sorry
