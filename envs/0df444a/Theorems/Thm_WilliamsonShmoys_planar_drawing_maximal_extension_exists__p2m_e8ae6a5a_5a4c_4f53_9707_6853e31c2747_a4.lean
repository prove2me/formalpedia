-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_exists__p2m_e8ae6a5a_5a4c_4f53_9707_6853e31c2747_a4
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_exists__p2m_e8ae6a5a_5a4c_4f53_9707_6853e31c2747_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T00:55:14.282039+00:00
-- url     : https://prove2.me/theorems/4d2d5a11-41cd-434a-8f62-802b33921d5f
-- title:
--   Maximal drawable supergraph on the same finite vertex type
-- statement:
--   Every drawable graph on a finite linearly ordered vertex type has a drawable supergraph on the same vertex type with no strictly larger drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension_exists__p2m_e8ae6a5a_5a4c_4f53_9707_6853e31c2747_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hDraw : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M := by sorry
