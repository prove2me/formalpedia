-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_bound_v4
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_bound_v4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T04:26:24.246238+00:00
-- url     : https://prove2.me/theorems/7106e376-e589-4b53-a920-5c22a8b941c8
-- title:
--   A maximal drawable graph meets the planar edge lower bound
-- statement:
--   A drawable graph on at least three vertices that has no strict drawable supergraph has at least 3|V|−6 edges. The proof route is to extend a maximal planar drawing to a triangulation (or otherwise establish the standard maximal-planar edge count); the hypothesis hmax states maximality among drawable supergraphs on the fixed vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_bound_v4
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M) :
    3 * (Fintype.card V : Int) - 6 ≤ (M.edgeSet.ncard : Int) := by sorry
