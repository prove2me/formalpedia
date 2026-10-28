-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_792d6233_0413_48c2_8c4d_fb4d15268d51
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count_792d6233_0413_48c2_8c4d_fb4d15268d51
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T18:48:58.784015+00:00
-- url     : https://prove2.me/theorems/a1d336b1-f975-4a54-a7fc-c4dfef1e43c2
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that has no strictly larger drawable supergraph has exactly 3|V|−6 edges. This child removes the Euler-counting geometry from the parent. A proof route is to show that maximality forces a triangulated planar embedding, then combine Euler’s formula with the fact that each edge contributes two face incidences. At three vertices, maximality forces the triangle and the same equation holds.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count_792d6233_0413_48c2_8c4d_fb4d15268d51
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hXdraw : WilliamsonShmoys.HasPlanarDrawingOn X)
    (hMax : ∀ Y : SimpleGraph V, X ≤ Y →
      WilliamsonShmoys.HasPlanarDrawingOn Y → Y = X) :
    3 * Fintype.card V = X.edgeSet.ncard + 6 := by
  sorry
