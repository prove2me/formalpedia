-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_has_face_certificate__p2m_53c17418_11ef_424f_a50a_b8723b415e73_a1
-- name    : WilliamsonShmoys.maximal_planar_has_face_certificate__p2m_53c17418_11ef_424f_a50a_b8723b415e73_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:48:09.77577+00:00
-- url     : https://prove2.me/theorems/176e07a1-5f1d-41f7-bcbc-8d41772c2d52
-- title:
--   Face certificate for a maximal planar graph
-- statement:
--   A maximal planar graph on at least three vertices has finite face data whose degrees are at least three and satisfy Euler’s formula and the face-edge incidence count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_PlanarTriangulationCertificate__p2m_92141bf6_e5aa_4060_bf2d_eb63ac46c206_a3

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_has_face_certificate__p2m_53c17418_11ef_424f_a50a_b8723b415e73_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) (hMax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) (hV : 3 ≤ Fintype.card V) : Nonempty (WilliamsonShmoys.PlanarTriangulationCertificate__p2m_92141bf6_e5aa_4060_bf2d_eb63ac46c206_a3 K) := by sorry
