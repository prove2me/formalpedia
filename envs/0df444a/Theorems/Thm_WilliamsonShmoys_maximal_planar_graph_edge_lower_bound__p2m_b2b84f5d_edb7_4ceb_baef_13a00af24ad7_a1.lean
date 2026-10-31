-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_lower_bound__p2m_b2b84f5d_edb7_4ceb_baef_13a00af24ad7_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_lower_bound__p2m_b2b84f5d_edb7_4ceb_baef_13a00af24ad7_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T06:07:06.847403+00:00
-- url     : https://prove2.me/theorems/4ab45211-21f9-4ad7-bbd8-2b8655cad493
-- title:
--   Maximal drawable graph edge lower bound
-- statement:
--   A drawable graph on at least three vertices that is maximal under drawable edge extensions has at least 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_lower_bound__p2m_b2b84f5d_edb7_4ceb_baef_13a00af24ad7_a1 {V : Type} [Fintype V] [LinearOrder V] (R : SimpleGraph V) (hDraw : HasPlanarDrawingOn R) (hV : 3 ≤ Fintype.card V) (hmax : ∀ S : SimpleGraph V, R.edgeSet ⊆ S.edgeSet → HasPlanarDrawingOn S → S.edgeSet ⊆ R.edgeSet) : 3 * Fintype.card V ≤ R.edgeSet.ncard + 6 := by sorry
