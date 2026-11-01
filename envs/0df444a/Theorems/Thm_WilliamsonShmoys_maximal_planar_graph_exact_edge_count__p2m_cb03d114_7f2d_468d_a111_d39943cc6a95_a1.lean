-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_exact_edge_count__p2m_cb03d114_7f2d_468d_a111_d39943cc6a95_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_exact_edge_count__p2m_cb03d114_7f2d_468d_a111_d39943cc6a95_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:29:02.740988+00:00
-- url     : https://prove2.me/theorems/b3b14217-54f7-4da9-9b6d-f0fddbb566d2
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no strict drawable supergraph on those vertices has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_exact_edge_count__p2m_cb03d114_7f2d_468d_a111_d39943cc6a95_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V,
      (∀ u v, N.Adj u v → P.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn P →
      ∀ u v, P.Adj u v → N.Adj u v) :
    3 * Fintype.card V = N.edgeSet.ncard + 6 := by sorry
