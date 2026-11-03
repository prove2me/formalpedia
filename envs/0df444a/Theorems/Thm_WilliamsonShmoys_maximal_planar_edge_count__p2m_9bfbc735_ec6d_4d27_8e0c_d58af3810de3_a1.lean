-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_9bfbc735_ec6d_4d27_8e0c_d58af3810de3_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_9bfbc735_ec6d_4d27_8e0c_d58af3810de3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:48:14.374819+00:00
-- url     : https://prove2.me/theorems/700bbd5b-00a3-4afe-b6e3-ec004e650a47
-- title:
--   Maximal planar graphs have the triangulation edge count
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open scoped BigOperators

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_9bfbc735_ec6d_4d27_8e0c_d58af3810de3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    3 * Fintype.card V - 6 = K.edgeSet.ncard := by sorry
