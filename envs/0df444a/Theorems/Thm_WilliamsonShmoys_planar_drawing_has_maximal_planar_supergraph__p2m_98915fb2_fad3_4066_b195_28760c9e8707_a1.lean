-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_planar_supergraph__p2m_98915fb2_fad3_4066_b195_28760c9e8707_a1
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_planar_supergraph__p2m_98915fb2_fad3_4066_b195_28760c9e8707_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:23:51.596359+00:00
-- url     : https://prove2.me/theorems/0f1ce812-dee0-4a44-8a54-cdde1b7fec7e
-- title:
--   Maximal drawable supergraph on the same vertices
-- statement:
--   Every graph with the specified planar drawing on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_has_maximal_planar_supergraph__p2m_98915fb2_fad3_4066_b195_28760c9e8707_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V) (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q) :
    ∃ R : SimpleGraph V, Q ≤ R ∧ WilliamsonShmoys.HasPlanarDrawingOn R ∧
      ∀ S : SimpleGraph V, R ≤ S → WilliamsonShmoys.HasPlanarDrawingOn S → S = R := by sorry
