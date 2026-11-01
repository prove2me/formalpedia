-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_1df68e30_02cf_4572_bf8a_d78917d2b48a_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_1df68e30_02cf_4572_bf8a_d78917d2b48a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:01:53.01976+00:00
-- url     : https://prove2.me/theorems/99986598-6392-4501-ac0d-a0cd3c835fd3
-- title:
--   Maximal planar drawing edge lower bound
-- statement:
--   A drawable graph on at least three vertices that has no drawable simple supergraph on the same vertex type with additional edges has at least 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_1df68e30_02cf_4572_bf8a_d78917d2b48a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ K : SimpleGraph V, L ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = L) :
    3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by sorry
