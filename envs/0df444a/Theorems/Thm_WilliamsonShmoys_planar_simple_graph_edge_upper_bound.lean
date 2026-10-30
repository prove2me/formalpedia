-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound
-- name    : WilliamsonShmoys.planar_simple_graph_edge_upper_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:09:54.344857+00:00
-- url     : https://prove2.me/theorems/f09608d6-fc03-4477-9211-fff559081512
-- title:
--   Euler upper bound for connected simple planar graphs
-- statement:
--   A connected simple graph with the specified planar drawing and at least three vertices has at most 3|V|−6 edges. This is the reusable Euler upper bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_upper_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : ∀ u v, Relation.ReflTransGen H.Adj u v)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
