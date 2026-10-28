-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_f624320d_e63d_47e0_83d6_ecbceca14194_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_f624320d_e63d_47e0_83d6_ecbceca14194_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:40:23.525394+00:00
-- url     : https://prove2.me/theorems/9e62a282-1660-478f-a7eb-09c81745fefa
-- title:
--   Maximal drawable supergraph extension
-- statement:
--   Every drawable simple graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal among drawable supergraphs and has at least as many edges as the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_f624320d_e63d_47e0_83d6_ecbceca14194_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M.edgeSet.ncard ≤ N.edgeSet.ncard ∧
      M ≤ N ∧
      (∀ K : SimpleGraph V,
        N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ N) ∧
      WilliamsonShmoys.HasPlanarDrawingOn N := by sorry
