-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph_exists__p2m_63a2cd28_190d_474c_9b63_884183b5c0a6_a1
-- name    : WilliamsonShmoys.planar_maximal_supergraph_exists__p2m_63a2cd28_190d_474c_9b63_884183b5c0a6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:30:04.766838+00:00
-- url     : https://prove2.me/theorems/e83255d4-a03b-497b-b93b-7d6db9d6a3b4
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex type that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_maximal_supergraph_exists__p2m_63a2cd28_190d_474c_9b63_884183b5c0a6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V,
        N.edgeSet ⊆ K.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet = N.edgeSet := by sorry
