-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_with_triangulated_edge_count
-- name    : WilliamsonShmoys.planar_drawing_completion_with_triangulated_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T22:53:34.293087+00:00
-- url     : https://prove2.me/theorems/36583a35-5b1f-4c70-ae55-691714c84535
-- title:
--   A drawable graph has a completion with the triangulation edge count
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices is contained in a drawable graph on the same vertices with exactly `3|V|−6` edges. A route is to choose an inclusion-maximal drawable supergraph, prove it is triangulated, and count with Euler’s formula; when there are exactly three vertices, the completion is the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_completion_with_triangulated_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
