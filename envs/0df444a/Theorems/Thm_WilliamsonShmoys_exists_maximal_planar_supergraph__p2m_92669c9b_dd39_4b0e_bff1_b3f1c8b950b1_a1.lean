-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_92669c9b_dd39_4b0e_bff1_b3f1c8b950b1_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_92669c9b_dd39_4b0e_bff1_b3f1c8b950b1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:35:55.868188+00:00
-- url     : https://prove2.me/theorems/c813e8d9-188c-4202-b644-d7aaf9123e11
-- title:
--   Existence of an inclusion-maximal planar supergraph
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertices that is inclusion-maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_92669c9b_dd39_4b0e_bff1_b3f1c8b950b1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      Set.Subset M.edgeSet N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ P : SimpleGraph V,
        Set.Subset N.edgeSet P.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn P →
        Set.Subset P.edgeSet N.edgeSet := by sorry
