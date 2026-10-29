-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_graph_edge_lower_bound
-- name    : WilliamsonShmoys.exists_planar_graph_edge_lower_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:29:41.338787+00:00
-- url     : https://prove2.me/theorems/b930043c-4820-417e-800b-91790181e1e6
-- title:
--   A drawable graph with the planar lower-bound edge count exists
-- statement:
--   For every finite linearly ordered vertex type with at least three elements, there is a graph on that vertex type that has a planar drawing under the supplied predicate and at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_graph_edge_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (hV : 3 <= Fintype.card V) :
    ∃ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V <= L.edgeSet.ncard + 6 := by sorry
