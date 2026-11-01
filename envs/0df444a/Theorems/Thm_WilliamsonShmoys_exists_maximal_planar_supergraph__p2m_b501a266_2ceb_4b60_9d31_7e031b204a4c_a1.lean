-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_b501a266_2ceb_4b60_9d31_7e031b204a4c_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_b501a266_2ceb_4b60_9d31_7e031b204a4c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:44:43.642248+00:00
-- url     : https://prove2.me/theorems/4d90f1b7-b2a8-462b-b2a8-5c5f2eedf8d9
-- title:
--   Existence of an edge-maximal drawable planar supergraph
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertices that is maximal under edge inclusion among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_b501a266_2ceb_4b60_9d31_7e031b204a4c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    ∃ M : SimpleGraph V,
      T.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V,
        M.edgeSet ⊆ N.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn N →
        N.edgeSet ⊆ M.edgeSet := by sorry
