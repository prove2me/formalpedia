-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_maximal_extension__p2m_31727deb_1ab6_43dd_805b_f9cbe6cd890f_a1
-- name    : WilliamsonShmoys.planar_drawable_maximal_extension__p2m_31727deb_1ab6_43dd_805b_f9cbe6cd890f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:33:49.101968+00:00
-- url     : https://prove2.me/theorems/76998751-2d00-4690-8bec-fa846df46441
-- title:
--   Extend a planar drawing to an inclusion-maximal drawable graph
-- statement:
--   Every drawable graph on a fixed finite ordered vertex type is contained in a drawable graph that has no strictly larger drawable supergraph on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawable_maximal_extension__p2m_31727deb_1ab6_43dd_805b_f9cbe6cd890f_a1
    {V : Type} [Fintype V] [LinearOrder V] (Y : SimpleGraph V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    ∃ Z : SimpleGraph V, Y ≤ Z ∧
      WilliamsonShmoys.HasPlanarDrawingOn Z ∧
      ∀ W : SimpleGraph V, Z ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W → W ≤ Z := by sorry
