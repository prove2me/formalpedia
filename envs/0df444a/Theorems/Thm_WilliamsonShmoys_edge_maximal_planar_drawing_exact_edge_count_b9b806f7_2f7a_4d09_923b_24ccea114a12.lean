-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_drawing_exact_edge_count_b9b806f7_2f7a_4d09_923b_24ccea114a12
-- name    : WilliamsonShmoys.edge_maximal_planar_drawing_exact_edge_count_b9b806f7_2f7a_4d09_923b_24ccea114a12
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T10:46:33.121863+00:00
-- url     : https://prove2.me/theorems/d42c8f91-ac47-4320-bc80-c3d77a1995cc
-- title:
--   Exact edge count for an edge-maximal planar drawing
-- statement:
--   Every finite simple graph with at least three vertices that has the supplied planar drawing and is maximal among planar supergraphs on the same vertex set has exactly 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_planar_drawing_exact_edge_count_b9b806f7_2f7a_4d09_923b_24ccea114a12
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : forall K : SimpleGraph V,
      M <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K <= M) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by sorry
