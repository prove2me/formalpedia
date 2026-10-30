-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_lower_bound__p2m_7592409d_0b44_4594_9ed9_df868002d7c4_a1
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound__p2m_7592409d_0b44_4594_9ed9_df868002d7c4_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:01:19.903621+00:00
-- url     : https://prove2.me/theorems/060f8740-15c3-4ae0-bb04-cbb0a26a05a1
-- title:
--   Maximal drawable graph edge lower bound
-- statement:
--   A drawable graph on at least three vertices that is maximal under drawable edge-set extensions has at least 3n − 6 edges. The new argument is the maximality-to-triangulation step: since the vertex type is finite, drawable edge extensions can be added until no more are possible; maximality identifies the resulting edge set with H. Show that each face in the resulting embedding is triangular, then apply Euler’s formula to obtain the lower bound. This child retains the maximality hypothesis and the n ≥ 3 boundary condition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound__p2m_7592409d_0b44_4594_9ed9_df868002d7c4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K ->
      Set.Subset H.edgeSet K.edgeSet ->
      H.edgeSet = K.edgeSet)
    (hV : 3 <= Fintype.card V) :
    3 * Fintype.card V <= H.edgeSet.ncard + 6 := by sorry
