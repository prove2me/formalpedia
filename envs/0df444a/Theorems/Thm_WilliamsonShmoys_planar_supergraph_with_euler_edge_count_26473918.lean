-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_euler_edge_count_26473918
-- name    : WilliamsonShmoys.planar_supergraph_with_euler_edge_count_26473918
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:02:07.402654+00:00
-- url     : https://prove2.me/theorems/5537debd-ad75-4f42-98bc-b8bfb46f5ce2
-- title:
--   Drawable graphs extend to a planar supergraph with Euler’s edge count
-- statement:
--   For any drawable finite simple graph on at least three vertices, there is a drawable supergraph on the same vertices with exactly three times the vertex count minus six edges. Extend the drawing by adding noncrossing edges until it is maximal; then every face is triangular, and Euler’s formula gives the stated count. The three-vertex boundary case is the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_with_euler_edge_count_26473918
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hGdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
