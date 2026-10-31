-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_mono_of_graph_le__p2m_a5cf4edc_e88b_40ef_a197_b0d2fda5eb44_a1
-- name    : WilliamsonShmoys.edge_count_mono_of_graph_le__p2m_a5cf4edc_e88b_40ef_a197_b0d2fda5eb44_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:50:55.023795+00:00
-- url     : https://prove2.me/theorems/c39ba1d1-7c96-4bdf-b948-1376f3552e7f
-- title:
--   Monotonicity of edge count under graph inclusion
-- statement:
--   If one finite simple graph is a subgraph of another on the same vertices, its edge count is no larger.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_mono_of_graph_le__p2m_a5cf4edc_e88b_40ef_a197_b0d2fda5eb44_a1 {V : Type} [Fintype V] [LinearOrder V] {G H : SimpleGraph V} (h : G ≤ H) : G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
