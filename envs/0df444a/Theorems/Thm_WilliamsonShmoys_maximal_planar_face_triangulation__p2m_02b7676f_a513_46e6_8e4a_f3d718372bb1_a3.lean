-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_triangulation__p2m_02b7676f_a513_46e6_8e4a_f3d718372bb1_a3
-- name    : WilliamsonShmoys.maximal_planar_face_triangulation__p2m_02b7676f_a513_46e6_8e4a_f3d718372bb1_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:45:18.332195+00:00
-- url     : https://prove2.me/theorems/18fad212-36ea-4c15-83d2-5b7bd6c85e9a
-- title:
--   Euler identity and triangular face count for maximal planar drawings
-- statement:
--   For a maximal drawable simple graph on at least three vertices, there is a face count satisfying Euler’s identity and the equality between three incidences per face and two incidences per edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_face_triangulation__p2m_02b7676f_a513_46e6_8e4a_f3d718372bb1_a3 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hMax : ∀ J : SimpleGraph V, H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J = H) (hV : 3 ≤ Fintype.card V) : ∃ f : ℕ, Fintype.card V + f = H.edgeSet.ncard + 2 ∧ 3 * f = 2 * H.edgeSet.ncard := by sorry
