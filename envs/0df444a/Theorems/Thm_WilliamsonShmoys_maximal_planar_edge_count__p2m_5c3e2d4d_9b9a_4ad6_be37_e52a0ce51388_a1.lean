-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_5c3e2d4d_9b9a_4ad6_be37_e52a0ce51388_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_5c3e2d4d_9b9a_4ad6_be37_e52a0ce51388_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:21:08.461508+00:00
-- url     : https://prove2.me/theorems/1863c0cc-84bc-4e3a-b61f-07ce03271d4c
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three finite vertices that has no proper drawable supergraph on those vertices has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_5c3e2d4d_9b9a_4ad6_be37_e52a0ce51388_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V,
      J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = J) :
    J.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
