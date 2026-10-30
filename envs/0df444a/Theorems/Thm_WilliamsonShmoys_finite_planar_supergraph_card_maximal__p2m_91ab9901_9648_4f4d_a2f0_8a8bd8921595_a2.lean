-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_planar_supergraph_card_maximal__p2m_91ab9901_9648_4f4d_a2f0_8a8bd8921595_a2
-- name    : WilliamsonShmoys_finite_planar_supergraph_card_maximal__p2m_91ab9901_9648_4f4d_a2f0_8a8bd8921595_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:59:24.311299+00:00
-- url     : https://prove2.me/theorems/0a87fba2-6594-4cd1-964e-d9bf54c0b030
-- title:
--   A drawable supergraph maximizing edge count
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertices containing it whose edge-set cardinality is at least that of every other drawable supergraph containing it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys_finite_planar_supergraph_card_maximal__p2m_91ab9901_9648_4f4d_a2f0_8a8bd8921595_a2 {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet →
        HasPlanarDrawingOn K → K.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
