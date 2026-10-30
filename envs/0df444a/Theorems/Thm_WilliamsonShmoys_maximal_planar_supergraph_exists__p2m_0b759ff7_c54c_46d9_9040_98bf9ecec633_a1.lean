-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exists__p2m_0b759ff7_c54c_46d9_9040_98bf9ecec633_a1
-- name    : WilliamsonShmoys_maximal_planar_supergraph_exists__p2m_0b759ff7_c54c_46d9_9040_98bf9ecec633_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:41:41.421068+00:00
-- url     : https://prove2.me/theorems/91ab9901-9648-4f4d-a2f0-8a8bd8921595
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every finite drawable graph has a drawable supergraph on the same vertices that is maximal among drawable supergraphs under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys_maximal_planar_supergraph_exists__p2m_0b759ff7_c54c_46d9_9040_98bf9ecec633_a1 {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet →
        HasPlanarDrawingOn K → K.edgeSet ⊆ H.edgeSet := by sorry
