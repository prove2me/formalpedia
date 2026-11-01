-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_a419e21a_2978_404e_8b1f_5dd1d0da8bd8_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_a419e21a_2978_404e_8b1f_5dd1d0da8bd8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:00:22.217575+00:00
-- url     : https://prove2.me/theorems/14be45b2-4af8-4477-b67a-6d2fa4a08c68
-- title:
--   A maximal drawable graph has the triangulation edge count
-- statement:
--   A drawable simple graph on at least three vertices that has no drawable strict supergraph has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_a419e21a_2978_404e_8b1f_5dd1d0da8bd8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K.edgeSet ⊂ L.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn L) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
