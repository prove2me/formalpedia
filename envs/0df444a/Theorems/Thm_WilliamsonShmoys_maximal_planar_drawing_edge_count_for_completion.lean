-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_for_completion
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_for_completion
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T07:20:07.456625+00:00
-- url     : https://prove2.me/theorems/77c4f8ee-3fa8-49eb-b12a-583ef660c388
-- title:
--   Euler edge count for a maximal planar completion
-- statement:
--   A graph on at least three vertices that has the specified planar drawing and is maximal under planar edge extensions has exactly three times its number of vertices minus six edges. The proof route is to show maximality forces a connected triangulation, then apply Euler’s formula; at three vertices the count is the triangle’s three edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_for_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet ⊆ K.edgeSet) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
