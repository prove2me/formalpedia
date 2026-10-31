-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_edge_count_upper_bound__p2m_429266ef_2658_4bcb_86f5_df3246663c92_a1
-- name    : WilliamsonShmoys.planar_graph_edge_count_upper_bound__p2m_429266ef_2658_4bcb_86f5_df3246663c92_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:21:15.318935+00:00
-- url     : https://prove2.me/theorems/517acab8-1dff-430a-88ba-b65381dc6f37
-- title:
--   Planar simple graph edge-count upper bound
-- statement:
--   Every drawable simple graph on at least three vertices has at most 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_edge_count_upper_bound__p2m_429266ef_2658_4bcb_86f5_df3246663c92_a1 {V : Type} [Fintype V] [LinearOrder V] (Z : SimpleGraph V) (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z) (hV : 3 ≤ Fintype.card V) : Z.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
