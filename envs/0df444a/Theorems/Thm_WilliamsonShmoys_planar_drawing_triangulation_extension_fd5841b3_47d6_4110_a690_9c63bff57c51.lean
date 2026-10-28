-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_fd5841b3_47d6_4110_a690_9c63bff57c51
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension_fd5841b3_47d6_4110_a690_9c63bff57c51
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T03:24:06.291736+00:00
-- url     : https://prove2.me/theorems/d64d0cba-1500-4321-b034-3d8ad04721cd
-- title:
--   Extend a planar drawing to a triangulation on fixed vertices
-- statement:
--   Every drawable simple graph on a finite ordered vertex set with at least three vertices has a drawable supergraph on the same vertex set with exactly 3|V|−6 edges. A proof can extend the drawing to an edge-maximal planar drawing, show it is a triangulation, and use Euler’s formula. The three-vertex case gives the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_triangulation_extension_fd5841b3_47d6_4110_a690_9c63bff57c51
    {V : Type} [Fintype V] [LinearOrder V]
    (hV : 3 <= Fintype.card V)
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V, P ≤ Q ∧
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      3 * Fintype.card V - 6 = Q.edgeSet.ncard := by sorry
