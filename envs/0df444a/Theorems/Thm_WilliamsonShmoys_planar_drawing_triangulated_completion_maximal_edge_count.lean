-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_completion_maximal_edge_count
-- name    : WilliamsonShmoys.planar_drawing_triangulated_completion_maximal_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T03:06:17.106968+00:00
-- url     : https://prove2.me/theorems/a15f106d-1a67-482b-a624-aaecb151ec34
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A planar graph on n ≥ 3 vertices that is maximal among planar supergraphs on the same vertex type has exactly 3n − 6 edges. The proof must establish that maximality makes the drawing a triangulation, then apply Euler’s formula and the face-edge incidence count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulated_completion_maximal_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMaximal : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K)
    (n : Nat)
    (hLarge : 3 ≤ n)
    (hcard : Fintype.card V = n) :
    K.edgeSet.ncard = 3 * n - 6 := by sorry
