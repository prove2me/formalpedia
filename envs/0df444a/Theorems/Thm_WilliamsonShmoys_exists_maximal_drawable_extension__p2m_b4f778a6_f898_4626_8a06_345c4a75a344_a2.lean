-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_extension__p2m_b4f778a6_f898_4626_8a06_345c4a75a344_a2
-- name    : WilliamsonShmoys.exists_maximal_drawable_extension__p2m_b4f778a6_f898_4626_8a06_345c4a75a344_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:46:46.093093+00:00
-- url     : https://prove2.me/theorems/f0ae2a89-338a-4b39-88cf-341f6f611f31
-- title:
--   A drawable graph has a maximal drawable supergraph on the same vertices
-- statement:
--   Every drawable graph on a finite vertex type is contained in a drawable supergraph that has no strictly larger drawable supergraph on those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_drawable_extension__p2m_b4f778a6_f898_4626_8a06_345c4a75a344_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by sorry
