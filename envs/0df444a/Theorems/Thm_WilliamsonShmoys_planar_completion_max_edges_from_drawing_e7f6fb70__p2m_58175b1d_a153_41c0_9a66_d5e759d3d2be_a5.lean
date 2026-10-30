-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_max_edges_from_drawing_e7f6fb70__p2m_58175b1d_a153_41c0_9a66_d5e759d3d2be_a5
-- name    : WilliamsonShmoys.planar_completion_max_edges_from_drawing_e7f6fb70__p2m_58175b1d_a153_41c0_9a66_d5e759d3d2be_a5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T01:51:41.749016+00:00
-- url     : https://prove2.me/theorems/9c6e361c-4d55-4494-87be-52db2dff7ab6
-- title:
--   Extend a planar drawing to a maximal planar graph
-- statement:
--   Any finite graph with a crossing-free drawing on at least three fixed vertices is contained in a graph on the same vertices with a crossing-free drawing and exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_completion_max_edges_from_drawing_e7f6fb70__p2m_58175b1d_a153_41c0_9a66_d5e759d3d2be_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    Exists fun K : SimpleGraph V =>
      (forall {u v}, H.Adj u v -> K.Adj u v) /\
      WilliamsonShmoys.HasPlanarDrawingOn K /\
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
