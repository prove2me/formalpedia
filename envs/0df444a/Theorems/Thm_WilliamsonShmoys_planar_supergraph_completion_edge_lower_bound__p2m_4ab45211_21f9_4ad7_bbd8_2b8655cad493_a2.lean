-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_completion_edge_lower_bound__p2m_4ab45211_21f9_4ad7_bbd8_2b8655cad493_a2
-- name    : WilliamsonShmoys.planar_supergraph_completion_edge_lower_bound__p2m_4ab45211_21f9_4ad7_bbd8_2b8655cad493_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:37:25.486822+00:00
-- url     : https://prove2.me/theorems/dbc1909c-e0b1-4b52-8a1f-f063e3dc8217
-- title:
--   Edge lower bound from planar supergraph completion
-- statement:
--   Every drawable finite simple graph with at least three vertices has a drawable supergraph on the same vertices whose edge count is at least `3|V|−6`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_completion_edge_lower_bound__p2m_4ab45211_21f9_4ad7_bbd8_2b8655cad493_a2 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : HasPlanarDrawingOn G) (hV : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, G.edgeSet ⊆ H.edgeSet ∧ HasPlanarDrawingOn H ∧ 3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by sorry
