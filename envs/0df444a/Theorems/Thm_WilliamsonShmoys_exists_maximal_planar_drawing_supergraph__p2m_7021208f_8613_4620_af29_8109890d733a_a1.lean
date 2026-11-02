-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_supergraph__p2m_7021208f_8613_4620_af29_8109890d733a_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_drawing_supergraph__p2m_7021208f_8613_4620_af29_8109890d733a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:56:28.060818+00:00
-- url     : https://prove2.me/theorems/5c7296d8-cb4f-4c5c-9e1f-d382ba5a4bb4
-- title:
--   Maximal drawable supergraph on a fixed finite vertex set
-- statement:
--   Every drawable simple graph on a finite ordered vertex type is contained in an inclusion-maximal drawable graph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_maximal_planar_drawing_supergraph__p2m_7021208f_8613_4620_af29_8109890d733a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V) (hS : WilliamsonShmoys.HasPlanarDrawingOn S) :
    ∃ T : SimpleGraph V,
      S ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧
        ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T := by sorry
