-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawing_exact_edge_count
-- name    : WilliamsonShmoys.maximal_drawing_exact_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T22:22:37.238762+00:00
-- url     : https://prove2.me/theorems/098373be-39db-41d3-b42b-1ea7a5a4a7c7
-- title:
--   A maximal planar drawing has the triangulation edge count
-- statement:
--   For a drawable simple graph on at least three vertices that is maximal among drawable supergraphs on those vertices, the edge count is 3n − 6. Show that maximality forces triangular faces, then combine Euler’s formula with face-edge incidence counting. The n = 3 case is K₃.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawing_exact_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hTdraw : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hTmax : ∀ U : SimpleGraph V,
      T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U ≤ T) :
    T.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
