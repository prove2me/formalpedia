-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_mono__p2m_c61a4fef_10c9_4ef4_8d71_ebe38bea863d_a1
-- name    : WilliamsonShmoys.planar_edge_count_mono__p2m_c61a4fef_10c9_4ef4_8d71_ebe38bea863d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:21:59.808383+00:00
-- url     : https://prove2.me/theorems/7f8f765a-614d-4d3a-b4eb-11ccd6db84d9
-- title:
--   Monotonicity of graph edge count
-- statement:
--   For finite vertex types, inclusion of simple graphs implies inclusion of their edge sets and hence monotonicity of edge count. This is the combinatorial step used after connected augmentation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_mono__p2m_c61a4fef_10c9_4ef4_8d71_ebe38bea863d_a1 {V : Type} [Fintype V] [LinearOrder V] (L H : SimpleGraph V) (hLH : L ≤ H) : L.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
