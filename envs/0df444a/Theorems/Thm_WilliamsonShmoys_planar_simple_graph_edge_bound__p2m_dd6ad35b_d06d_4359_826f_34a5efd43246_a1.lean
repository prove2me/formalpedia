-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_dd6ad35b_d06d_4359_826f_34a5efd43246_a1
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_dd6ad35b_d06d_4359_826f_34a5efd43246_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:03:28.984054+00:00
-- url     : https://prove2.me/theorems/898ed614-bb9e-4a02-a507-ff39f26b30a9
-- title:
--   Planar simple graph edge bound
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_dd6ad35b_d06d_4359_826f_34a5efd43246_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : 3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by sorry
