-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph__p2m_995fdaa3_113b_42c8_81af_6ce1c08f331a_a1
-- name    : WilliamsonShmoys.planar_maximal_supergraph__p2m_995fdaa3_113b_42c8_81af_6ce1c08f331a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:25:01.214883+00:00
-- url     : https://prove2.me/theorems/cd0f16e5-b195-4f79-b4c4-7fd769dbac9a
-- title:
--   Every finite drawable graph has a maximal drawable supergraph
-- statement:
--   A drawable graph on a finite vertex type has a drawable supergraph on the same vertices that is maximal under edge-set inclusion among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_maximal_supergraph__p2m_995fdaa3_113b_42c8_81af_6ce1c08f331a_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) : ∃ N : SimpleGraph V, M.edgeSet ⊆ N.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧ ∀ Q : SimpleGraph V, N.edgeSet ⊆ Q.edgeSet → WilliamsonShmoys.HasPlanarDrawingOn Q → Q.edgeSet = N.edgeSet := by sorry
