-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_lower_bound_retry7_f81c96b6_b51d_4165_8b99_52e367cbc589_triangulation_extension
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count_lower_bound_retry7_f81c96b6_b51d_4165_8b99_52e367cbc589_triangulation_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:53:41.006491+00:00
-- url     : https://prove2.me/theorems/7e19ea7b-3a89-414b-9efd-1274176ad974
-- title:
--   Extension of a finite planar graph to a triangulation
-- statement:
--   Every planar simple graph on at least three fixed vertices is a subgraph of a planar simple graph on the same vertices whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_count_lower_bound_retry7_f81c96b6_b51d_4165_8b99_52e367cbc589_triangulation_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ T : SimpleGraph V,
      G ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧
        3 * Fintype.card V = T.edgeSet.ncard + 6 := by sorry
