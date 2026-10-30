-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_same_vertices
-- name    : WilliamsonShmoys.planar_completion_same_vertices
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:36:42.637357+00:00
-- url     : https://prove2.me/theorems/6f9ab176-bb29-48fd-ba5b-d05d0a4c6c8d
-- title:
--   Completion of a planar drawing to a triangulation on the same vertices
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices has a drawable supergraph on the same vertices whose edge count is exactly three times the number of vertices minus six. Prove this by inserting noncrossing edges into faces until the drawing is triangulated, then apply Euler’s formula. This removes the geometric completion and counting work from the parent; the parent only uses maximality to identify the completion with the original graph. The child is stronger than the target and reusable for any drawable graph, but its planar triangulation argument remains the main proof obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_completion_same_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z) :
    ∃ W : SimpleGraph V,
      Z ≤ W ∧ WilliamsonShmoys.HasPlanarDrawingOn W ∧
        3 * Fintype.card V = W.edgeSet.ncard + 6 := by sorry
