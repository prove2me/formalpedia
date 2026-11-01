-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_f88e8c23_22a3_4ff9_b09b_4991384a83f2_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_f88e8c23_22a3_4ff9_b09b_4991384a83f2_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:14:12.938735+00:00
-- url     : https://prove2.me/theorems/a01716d8-a871-45fb-bee6-57d4a8a808ae
-- title:
--   Maximal planar drawing edge lower bound
-- statement:
--   A drawable finite simple graph on at least three vertices that is maximal under drawable edge-set extensions has at least 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_f88e8c23_22a3_4ff9_b09b_4991384a83f2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ J : SimpleGraph V,
      H.edgeSet ⊆ J.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn J →
      J.edgeSet ⊆ H.edgeSet) :
    3 * Fintype.card V - 6 ≤ H.edgeSet.ncard := by sorry
