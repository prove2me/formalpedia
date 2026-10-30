-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound__p2m_94c3c327_8601_4c2d_adbc_08897459bc6e_a1
-- name    : WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_94c3c327_8601_4c2d_adbc_08897459bc6e_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:59:48.539437+00:00
-- url     : https://prove2.me/theorems/aba97578-a55f-467d-b26f-e953a5f6767e
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   Every finite simple graph with at least three vertices and a crossing-free drawing has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_94c3c327_8601_4c2d_adbc_08897459bc6e_a1
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hG : HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry
