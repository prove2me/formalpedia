-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_f4d7c237_0776_4adb_8bad_5150d3e32462_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_f4d7c237_0776_4adb_8bad_5150d3e32462_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:01:21.769963+00:00
-- url     : https://prove2.me/theorems/3b70d152-dbfb-4f09-8d03-767be9da3cd3
-- title:
--   Euler bound for edge-maximal drawable graphs
-- statement:
--   A drawable finite simple graph on at least three vertices that is maximal under drawable edge-set extensions satisfies the Euler edge bound. The intended proof shows maximality forces a connected triangulated plane embedding, then applies Euler’s formula and counts face-edge incidences.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_f4d7c237_0776_4adb_8bad_5150d3e32462_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K → K.edgeSet = H.edgeSet) :
    H.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  sorry
