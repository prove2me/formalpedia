-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_lower_bound__p2m_b3b14217_54f7_4da9_9b6d_f0fddbb566d2_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_lower_bound__p2m_b3b14217_54f7_4da9_9b6d_f0fddbb566d2_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:38:58.911319+00:00
-- url     : https://prove2.me/theorems/9d0243ad-5518-4310-b6ca-96e7e23d454c
-- title:
--   Maximal drawable graph edge lower bound
-- statement:
--   If a drawable simple graph on at least three vertices has no drawable strict supergraph on the same vertex set, it has at least three times its number of vertices minus six edges. The independent proof route is to show maximality forces every face in the drawing to be triangular: a face with a longer boundary permits a noncrossing diagonal and hence a drawable supergraph, contradicting `hmax`. Combine triangular face counting with Euler’s formula to obtain the inequality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_lower_bound__p2m_b3b14217_54f7_4da9_9b6d_f0fddbb566d2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V,
      (∀ u v, N.Adj u v → P.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn P →
      ∀ u v, P.Adj u v → N.Adj u v) :
    3 * Fintype.card V ≤ N.edgeSet.ncard + 6 := by sorry
