-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_92669c9b_dd39_4b0e_bff1_b3f1c8b950b1_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_92669c9b_dd39_4b0e_bff1_b3f1c8b950b1_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T20:35:57.515664+00:00
-- url     : https://prove2.me/theorems/90c7a03c-a708-4ce0-8e8e-3fca3bf8a16d
-- title:
--   Exact edge count of an inclusion-maximal planar graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three finite vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_92669c9b_dd39_4b0e_bff1_b3f1c8b950b1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ P : SimpleGraph V,
      Set.Subset N.edgeSet P.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn P →
      Set.Subset P.edgeSet N.edgeSet) :
    3 * Fintype.card V = N.edgeSet.ncard + 6 := by sorry
