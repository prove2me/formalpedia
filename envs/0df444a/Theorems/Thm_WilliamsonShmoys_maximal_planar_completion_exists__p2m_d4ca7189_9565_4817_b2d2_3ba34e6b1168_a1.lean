-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_exists__p2m_d4ca7189_9565_4817_b2d2_3ba34e6b1168_a1
-- name    : WilliamsonShmoys.maximal_planar_completion_exists__p2m_d4ca7189_9565_4817_b2d2_3ba34e6b1168_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:54:53.201448+00:00
-- url     : https://prove2.me/theorems/13d6333d-8327-4de0-a7db-2786f76107ad
-- title:
--   Finite maximal drawable supergraph extension
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal under edge inclusion among drawable supergraphs. No lower bound on the number of vertices is needed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_completion_exists__p2m_d4ca7189_9565_4817_b2d2_3ba34e6b1168_a1 {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V) (hDraw : HasPlanarDrawingOn Q) : ∃ R : SimpleGraph V, Q.edgeSet ⊆ R.edgeSet ∧ HasPlanarDrawingOn R ∧ (∀ S : SimpleGraph V, R.edgeSet ⊆ S.edgeSet → HasPlanarDrawingOn S → S.edgeSet ⊆ R.edgeSet) := by sorry
