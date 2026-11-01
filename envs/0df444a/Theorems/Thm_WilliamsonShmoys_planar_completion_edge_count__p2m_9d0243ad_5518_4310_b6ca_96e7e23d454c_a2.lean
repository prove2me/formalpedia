-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_edge_count__p2m_9d0243ad_5518_4310_b6ca_96e7e23d454c_a2
-- name    : WilliamsonShmoys.planar_completion_edge_count__p2m_9d0243ad_5518_4310_b6ca_96e7e23d454c_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:54:13.100506+00:00
-- url     : https://prove2.me/theorems/102f4bfa-075e-4b5b-84e9-4b6c34bfa40c
-- title:
--   Planar completion with the maximal planar edge count
-- statement:
--   Every finite drawable simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly 3|V|−6 edges. The child strengthens the target by removing the maximality assumption on the input graph: it asserts existence of a full-edge planar completion. A proof route is to normalize the finite arc drawing to a plane embedding, connect components and triangulate its faces, then apply Euler’s formula. The condition |V| ≥ 3 covers the boundary case, where the completion is K₃. The main remaining obligation is formalizing the topological normalization and triangulation argument for the supplied arbitrary-arc predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_completion_edge_count__p2m_9d0243ad_5518_4310_b6ca_96e7e23d454c_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V,
      (∀ u v, N.Adj u v → P.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      3 * Fintype.card V = P.edgeSet.ncard + 6 := by
  sorry
