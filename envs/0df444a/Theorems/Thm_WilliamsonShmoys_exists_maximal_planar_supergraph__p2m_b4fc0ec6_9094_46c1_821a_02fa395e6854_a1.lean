-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_b4fc0ec6_9094_46c1_821a_02fa395e6854_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_b4fc0ec6_9094_46c1_821a_02fa395e6854_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:53:19.713208+00:00
-- url     : https://prove2.me/theorems/c3e4c921-775b-4afc-815f-a590e3d69c46
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph is contained in an inclusion-maximal drawable simple graph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_b4fc0ec6_9094_46c1_821a_02fa395e6854_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V, N ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = N := by sorry
