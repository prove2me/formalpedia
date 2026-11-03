-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_5e34af62_bc93_4e27_8f77_f0a9265acaf1_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_5e34af62_bc93_4e27_8f77_f0a9265acaf1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:23:00.749204+00:00
-- url     : https://prove2.me/theorems/b1eeea0d-0264-4037-a9be-26c96369c701
-- title:
--   Maximal drawable graphs have the triangulation edge count
-- statement:
--   A drawable simple graph on at least three finite vertices that has no strictly larger drawable supergraph on those vertices has exactly $3|V|-6$ edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_5e34af62_bc93_4e27_8f77_f0a9265acaf1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ H : SimpleGraph V, K ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
