-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph__p2m_d270c124_96c5_427a_8655_88aa20edeadc_a1
-- name    : WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_d270c124_96c5_427a_8655_88aa20edeadc_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T01:00:29.211728+00:00
-- url     : https://prove2.me/theorems/2b5c1009-a179-4553-a4ff-0d018d6fc875
-- title:
--   Connected planar supergraph augmentation
-- statement:
--   Every finite graph with at least three vertices and a crossing-free drawing has a connected planar supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_d270c124_96c5_427a_8655_88aa20edeadc_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, H ≤ K ∧ K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
