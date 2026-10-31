-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_upper_bound__p2m_b2b84f5d_edb7_4ceb_baef_13a00af24ad7_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_upper_bound__p2m_b2b84f5d_edb7_4ceb_baef_13a00af24ad7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:07:05.114795+00:00
-- url     : https://prove2.me/theorems/ddfe16f2-466b-4eda-98ed-20e5107df448
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   Every simply drawable graph on at least three vertices has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_upper_bound__p2m_b2b84f5d_edb7_4ceb_baef_13a00af24ad7_a1 {V : Type} [Fintype V] [LinearOrder V] (R : SimpleGraph V) (hDraw : HasPlanarDrawingOn R) (hV : 3 ≤ Fintype.card V) : R.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
