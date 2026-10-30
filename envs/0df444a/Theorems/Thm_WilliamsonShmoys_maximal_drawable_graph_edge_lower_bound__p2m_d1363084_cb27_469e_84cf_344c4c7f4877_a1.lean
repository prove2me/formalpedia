-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_lower_bound__p2m_d1363084_cb27_469e_84cf_344c4c7f4877_a1
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound__p2m_d1363084_cb27_469e_84cf_344c4c7f4877_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:03:56.348348+00:00
-- url     : https://prove2.me/theorems/975201d3-ed40-44be-a94c-66f3df904250
-- title:
--   Edge bound for maximal drawable graphs
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has at least 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound__p2m_d1363084_cb27_469e_84cf_344c4c7f4877_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ H : SimpleGraph V,
      K ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ K)
    (hcard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ K.edgeFinset.card := by sorry
