-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_lower_bound_12627fe4_bb8b_4611_a4bf_2ba10834172b
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count_lower_bound_12627fe4_bb8b_4611_a4bf_2ba10834172b
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:41:23.018431+00:00
-- url     : https://prove2.me/theorems/c13714b8-e9ba-4b1e-a0d0-6f42cfb5903d
-- title:
--   Maximal drawable graphs have the triangulation edge count
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertices has at least three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count_lower_bound_12627fe4_bb8b_4611_a4bf_2ba10834172b
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hLdraw : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by sorry
