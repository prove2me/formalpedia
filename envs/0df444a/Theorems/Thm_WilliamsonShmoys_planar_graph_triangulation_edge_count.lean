-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_triangulation_edge_count
-- name    : WilliamsonShmoys.planar_graph_triangulation_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T14:42:10.553952+00:00
-- url     : https://prove2.me/theorems/a0db33ba-3005-42fa-b298-99aa0ff71c0b
-- title:
--   Triangulate a finite planar graph without adding vertices
-- statement:
--   Extend the given planar graph, without changing its vertices, to a planar graph whose edge count is exactly 3|V|−6, while retaining all original edges. The explicit cardinality monotonicity clause lets the parent use the result without depending on a particular SimpleGraph edge-set API.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_triangulation_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V,
      T ≤ U ∧
      WilliamsonShmoys.HasPlanarDrawingOn U ∧
      T.edgeSet.ncard ≤ U.edgeSet.ncard ∧
      U.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
