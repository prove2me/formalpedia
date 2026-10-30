-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_ge__p2m_6af46978_2916_4816_b606_4f4cb75b2f24_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_ge__p2m_6af46978_2916_4816_b606_4f4cb75b2f24_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T04:22:59.984576+00:00
-- url     : https://prove2.me/theorems/ca3692fe-9bc0-47df-8504-9567727a0d1c
-- title:
--   A maximal drawable graph reaches the planar edge bound
-- statement:
--   A drawable graph on at least three vertices that has no drawable proper supergraph on those vertices has at least 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_ge__p2m_6af46978_2916_4816_b606_4f4cb75b2f24_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : forall M : SimpleGraph V,
      L <= M -> WilliamsonShmoys.HasPlanarDrawingOn M -> M = L) :
    3 * Fintype.card V - 6 <= L.edgeSet.ncard := by sorry
