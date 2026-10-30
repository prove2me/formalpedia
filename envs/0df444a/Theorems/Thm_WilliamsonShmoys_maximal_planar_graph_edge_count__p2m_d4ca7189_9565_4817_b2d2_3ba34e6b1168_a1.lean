-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_d4ca7189_9565_4817_b2d2_3ba34e6b1168_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_d4ca7189_9565_4817_b2d2_3ba34e6b1168_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:54:56.112126+00:00
-- url     : https://prove2.me/theorems/b2b84f5d-edb7-4ceb-baef-13a00af24ad7
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that admits no drawable strict edge-supergraph has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_d4ca7189_9565_4817_b2d2_3ba34e6b1168_a1 {V : Type} [Fintype V] [LinearOrder V] (R : SimpleGraph V) (hDraw : HasPlanarDrawingOn R) (hV : 3 ≤ Fintype.card V) (hmax : ∀ S : SimpleGraph V, R.edgeSet ⊆ S.edgeSet → HasPlanarDrawingOn S → S.edgeSet ⊆ R.edgeSet) : R.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
