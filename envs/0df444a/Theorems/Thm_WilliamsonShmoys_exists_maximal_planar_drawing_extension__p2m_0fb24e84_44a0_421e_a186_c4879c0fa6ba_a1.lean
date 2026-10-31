-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_extension__p2m_0fb24e84_44a0_421e_a186_c4879c0fa6ba_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_drawing_extension__p2m_0fb24e84_44a0_421e_a186_c4879c0fa6ba_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:53:49.589196+00:00
-- url     : https://prove2.me/theorems/7bfe2f9e-080d-4b6e-9d97-8c2f9065d4c3
-- title:
--   Existence of an inclusion-maximal planar drawing extension
-- statement:
--   Every finite drawable graph has a drawable supergraph on the same vertices that has no strictly larger drawable supergraph on those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_drawing_extension__p2m_0fb24e84_44a0_421e_a186_c4879c0fa6ba_a1 {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        L.edgeSet ⊆ M.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M.edgeSet = L.edgeSet := by sorry
