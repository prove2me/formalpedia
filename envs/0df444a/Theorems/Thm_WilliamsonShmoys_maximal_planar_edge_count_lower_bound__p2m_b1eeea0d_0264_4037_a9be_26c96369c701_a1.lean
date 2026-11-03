-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_b1eeea0d_0264_4037_a9be_26c96369c701_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_b1eeea0d_0264_4037_a9be_26c96369c701_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:33:12.864076+00:00
-- url     : https://prove2.me/theorems/42928b97-f6a9-47a4-921a-031377856976
-- title:
--   Maximal drawable graphs meet the triangulation lower bound
-- statement:
--   If a drawable simple graph on at least three finite vertices has no strictly larger drawable supergraph on those vertices, then it has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_b1eeea0d_0264_4037_a9be_26c96369c701_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ H : SimpleGraph V, K ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ K) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by sorry
