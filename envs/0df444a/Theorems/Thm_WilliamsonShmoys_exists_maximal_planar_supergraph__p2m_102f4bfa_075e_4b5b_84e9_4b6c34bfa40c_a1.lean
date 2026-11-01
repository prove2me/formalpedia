-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_102f4bfa_075e_4b5b_84e9_4b6c34bfa40c_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_102f4bfa_075e_4b5b_84e9_4b6c34bfa40c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:11:19.101114+00:00
-- url     : https://prove2.me/theorems/e34751cd-edcb-44e6-9310-401a78916d54
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertex set whose edge count is maximal among its drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_102f4bfa_075e_4b5b_84e9_4b6c34bfa40c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V,
      (∀ u v, N.Adj u v → P.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      (∀ Q : SimpleGraph V,
        (∀ u v, P.Adj u v → Q.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn Q →
        Q.edgeSet.ncard ≤ P.edgeSet.ncard) := by
  sorry
