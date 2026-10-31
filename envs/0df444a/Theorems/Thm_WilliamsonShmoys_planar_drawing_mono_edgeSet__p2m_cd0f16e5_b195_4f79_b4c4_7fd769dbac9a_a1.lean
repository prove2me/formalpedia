-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_mono_edgeSet__p2m_cd0f16e5_b195_4f79_b4c4_7fd769dbac9a_a1
-- name    : WilliamsonShmoys.planar_drawing_mono_edgeSet__p2m_cd0f16e5_b195_4f79_b4c4_7fd769dbac9a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:31:08.812232+00:00
-- url     : https://prove2.me/theorems/ad138633-e7ef-49fa-9799-391d263d507f
-- title:
--   Planar drawing is preserved when edges are removed
-- statement:
--   If one graph's edge set is contained in another's, any crossing-free drawing of the larger graph is also a crossing-free drawing of the smaller graph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_mono_edgeSet__p2m_cd0f16e5_b195_4f79_b4c4_7fd769dbac9a_a1 {V : Type} [Fintype V] [LinearOrder V] {A B : SimpleGraph V} (hsub : B.edgeSet ⊆ A.edgeSet) : WilliamsonShmoys.HasPlanarDrawingOn A → WilliamsonShmoys.HasPlanarDrawingOn B := by sorry
