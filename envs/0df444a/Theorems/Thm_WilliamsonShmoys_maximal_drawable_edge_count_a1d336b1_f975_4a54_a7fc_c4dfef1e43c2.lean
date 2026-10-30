-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_a1d336b1_f975_4a54_a7fc_c4dfef1e43c2
-- name    : WilliamsonShmoys.maximal_drawable_edge_count_a1d336b1_f975_4a54_a7fc_c4dfef1e43c2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:37:07.798356+00:00
-- url     : https://prove2.me/theorems/4a1dd925-5090-4015-a463-fc64e2971e4a
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertices has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_count_a1d336b1_f975_4a54_a7fc_c4dfef1e43c2
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hYdraw : WilliamsonShmoys.HasPlanarDrawingOn Y)
    (hMax : ∀ Z : SimpleGraph V, Y ≤ Z →
      WilliamsonShmoys.HasPlanarDrawingOn Z → Z = Y) :
    3 * Fintype.card V = Y.edgeSet.ncard + 6 := by sorry
