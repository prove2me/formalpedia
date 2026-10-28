-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion
-- name    : WilliamsonShmoys.planar_drawing_triangulation_completion
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T03:29:59.062148+00:00
-- url     : https://prove2.me/theorems/9d3b0cae-f0d0-4db2-b1f8-af5009529476
-- title:
--   Triangulation completion for a finite planar drawing
-- statement:
--   Every finite graph with a crossing-free drawing and at least three vertices can be extended, on the same vertex set, to a crossing-free triangulation with exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V,
      P ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q ∧
        3 * Fintype.card V - 6 = Q.edgeSet.ncard := by sorry
