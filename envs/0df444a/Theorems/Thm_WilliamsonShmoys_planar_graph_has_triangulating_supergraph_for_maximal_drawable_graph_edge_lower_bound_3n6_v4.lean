-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulating_supergraph_for_maximal_drawable_graph_edge_lower_bound_3n6_v4
-- name    : WilliamsonShmoys.planar_graph_has_triangulating_supergraph_for_maximal_drawable_graph_edge_lower_bound_3n6_v4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T07:43:27.951429+00:00
-- url     : https://prove2.me/theorems/6eb3677d-c5b7-4cce-9ed6-67452c3da2ca
-- title:
--   Every drawable graph extends to a triangulation on the same vertices
-- statement:
--   A drawable simple graph on a finite ordered vertex type with at least three vertices has a drawable supergraph on the same vertex type with exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_has_triangulating_supergraph_for_maximal_drawable_graph_edge_lower_bound_3n6_v4
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P) :
    Exists fun Q : SimpleGraph V =>
      P <= Q ∧
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      Q.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
