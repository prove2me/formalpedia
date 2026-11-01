-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edge_count__p2m_202bf50d_736f_4a11_9464_01f4251d3269_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_202bf50d_736f_4a11_9464_01f4251d3269_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:08:24.401207+00:00
-- url     : https://prove2.me/theorems/f88e8c23-22a3-4ff9-b09b-4991384a83f2
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that admits no drawable simple supergraph with additional edges has exactly 3|V| − 6 edges. Prove this by showing maximality forces a triangulation of the sphere, then use Euler’s formula and count each face boundary; treat the three-vertex case directly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_202bf50d_736f_4a11_9464_01f4251d3269_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ J : SimpleGraph V,
      H.edgeSet ⊆ J.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn J →
      J.edgeSet ⊆ H.edgeSet) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
