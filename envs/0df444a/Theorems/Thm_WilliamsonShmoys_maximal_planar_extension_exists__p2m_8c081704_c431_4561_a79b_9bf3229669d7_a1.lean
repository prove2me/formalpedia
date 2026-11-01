-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_exists__p2m_8c081704_c431_4561_a79b_9bf3229669d7_a1
-- name    : WilliamsonShmoys.maximal_planar_extension_exists__p2m_8c081704_c431_4561_a79b_9bf3229669d7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:00:29.858945+00:00
-- url     : https://prove2.me/theorems/bdc3b847-9c7d-4952-b797-9d04867ba893
-- title:
--   Existence of an edge-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex set has a drawable supergraph on the same vertices that is maximal under adding edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_extension_exists__p2m_8c081704_c431_4561_a79b_9bf3229669d7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ P : SimpleGraph V,
        N.edgeSet ⊆ P.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn P →
        P.edgeSet = N.edgeSet := by
  sorry
