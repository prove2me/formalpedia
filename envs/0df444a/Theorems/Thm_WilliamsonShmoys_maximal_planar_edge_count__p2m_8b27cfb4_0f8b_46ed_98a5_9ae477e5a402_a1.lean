-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_8b27cfb4_0f8b_46ed_98a5_9ae477e5a402_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_8b27cfb4_0f8b_46ed_98a5_9ae477e5a402_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:08:37.822985+00:00
-- url     : https://prove2.me/theorems/9c3c045f-d7b5-4c10-ba62-84eac30669c7
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open scoped BigOperators

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_8b27cfb4_0f8b_46ed_98a5_9ae477e5a402_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K <= L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
