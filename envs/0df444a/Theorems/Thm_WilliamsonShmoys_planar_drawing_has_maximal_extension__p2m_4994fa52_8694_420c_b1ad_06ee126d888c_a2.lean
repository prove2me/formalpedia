-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension__p2m_4994fa52_8694_420c_b1ad_06ee126d888c_a2
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_4994fa52_8694_420c_b1ad_06ee126d888c_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:22:37.051983+00:00
-- url     : https://prove2.me/theorems/291e0450-6b44-4101-bed6-3a9f92eefd35
-- title:
--   A drawable graph has a maximal drawable extension
-- statement:
--   Every drawable graph on a finite ordered vertex type is contained in a drawable graph that is maximal under inclusion among drawable graphs on that type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_4994fa52_8694_420c_b1ad_06ee126d888c_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ (J : SimpleGraph V),
        H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ H := by
  sorry
