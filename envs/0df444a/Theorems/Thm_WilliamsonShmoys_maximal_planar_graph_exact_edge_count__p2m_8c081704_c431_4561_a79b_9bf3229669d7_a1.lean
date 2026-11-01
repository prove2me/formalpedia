-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_exact_edge_count__p2m_8c081704_c431_4561_a79b_9bf3229669d7_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_exact_edge_count__p2m_8c081704_c431_4561_a79b_9bf3229669d7_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:00:31.728008+00:00
-- url     : https://prove2.me/theorems/deeb4758-cfa0-4f01-9d35-86cdfd6516a4
-- title:
--   Exact edge count for a maximal drawable planar graph
-- statement:
--   An edge-maximal drawable simple graph with at least three vertices has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_exact_edge_count__p2m_8c081704_c431_4561_a79b_9bf3229669d7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ P : SimpleGraph V,
      N.edgeSet ⊆ P.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn P →
      P.edgeSet = N.edgeSet) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
