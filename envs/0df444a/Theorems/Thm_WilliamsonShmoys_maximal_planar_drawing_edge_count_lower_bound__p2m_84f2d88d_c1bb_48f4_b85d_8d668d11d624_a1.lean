-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound__p2m_84f2d88d_c1bb_48f4_b85d_8d668d11d624_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_84f2d88d_c1bb_48f4_b85d_8d668d11d624_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:23:15.239149+00:00
-- url     : https://prove2.me/theorems/aad1f7a7-a04a-47ce-bdaf-91f7c06a5480
-- title:
--   Lower edge bound for an inclusion-maximal planar drawing
-- statement:
--   For a drawable graph on at least three vertices, inclusion maximality among drawable supergraphs forces at least 3n−6 edges. This isolates the triangulation consequence of maximality and Euler counting. A proof route is to connect components by drawable edges, show maximality forces every face to be triangular, then use Euler’s formula and count edge incidences on faces. The n=3 boundary gives the triangle and satisfies the inequality with equality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_84f2d88d_c1bb_48f4_b85d_8d668d11d624_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by sorry
