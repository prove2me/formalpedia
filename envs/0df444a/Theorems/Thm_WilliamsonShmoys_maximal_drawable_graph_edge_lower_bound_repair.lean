-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_lower_bound_repair
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound_repair
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T21:53:29.030499+00:00
-- url     : https://prove2.me/theorems/5a848f27-da77-4398-8f59-dbcec5fc82ba
-- title:
--   Maximal drawable graph edge lower bound
-- statement:
--   If a drawable graph on at least three vertices is maximal among drawable supergraphs on the same vertex type, it has at least three times its vertex count minus six edges. A proof route is to augment the drawing to a triangulation on the same vertices, use maximality to identify the augmentation with the original graph, and count triangulation edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound_repair
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by sorry
