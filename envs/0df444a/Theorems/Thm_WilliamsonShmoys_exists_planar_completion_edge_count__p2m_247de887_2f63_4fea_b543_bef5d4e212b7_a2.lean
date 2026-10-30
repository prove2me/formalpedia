-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_completion_edge_count__p2m_247de887_2f63_4fea_b543_bef5d4e212b7_a2
-- name    : WilliamsonShmoys.exists_planar_completion_edge_count__p2m_247de887_2f63_4fea_b543_bef5d4e212b7_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:10:40.743504+00:00
-- url     : https://prove2.me/theorems/a99632a3-b093-44bf-a9c2-781640e2eb8d
-- title:
--   Planar completion with the maximal planar edge count
-- statement:
--   Every drawable finite simple graph with at least three vertices is contained in a drawable graph on the same vertex type whose edge count is three times the vertex count minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_edge_count_7369a359

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_planar_completion_edge_count__p2m_247de887_2f63_4fea_b543_bef5d4e212b7_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDraw : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ HasPlanarDrawingOn K ∧
        K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
