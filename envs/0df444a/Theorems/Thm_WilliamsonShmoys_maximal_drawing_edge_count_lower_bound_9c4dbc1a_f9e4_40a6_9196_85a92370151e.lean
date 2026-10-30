-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawing_edge_count_lower_bound_9c4dbc1a_f9e4_40a6_9196_85a92370151e
-- name    : WilliamsonShmoys.maximal_drawing_edge_count_lower_bound_9c4dbc1a_f9e4_40a6_9196_85a92370151e
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:02:08.890133+00:00
-- url     : https://prove2.me/theorems/eb6914d5-485c-4dc4-9b8a-ddb875e9bebb
-- title:
--   Maximal planar drawing edge count lower bound
-- statement:
--   A drawable simple graph on at least three vertices that has no drawable strict supergraph has at least three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawing_edge_count_lower_bound_9c4dbc1a_f9e4_40a6_9196_85a92370151e
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      G.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet ⊆ G.edgeSet) :
    3 * Fintype.card V - 6 <= G.edgeSet.ncard := by
  sorry
