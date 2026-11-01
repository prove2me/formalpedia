-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_602c691a_8d1a_4dfe_88c6_7f0f95c89b91_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_602c691a_8d1a_4dfe_88c6_7f0f95c89b91_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:15:34.857364+00:00
-- url     : https://prove2.me/theorems/4e7460fe-69a1-4b10-9830-48d825fa3caa
-- title:
--   A planar drawing has a maximal planar supergraph on the same vertices
-- statement:
--   Every graph with a crossing-free drawing has a supergraph on the same finite vertex set that admits such a drawing and is maximal under adding edges while preserving that property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_602c691a_8d1a_4dfe_88c6_7f0f95c89b91_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
