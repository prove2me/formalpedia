-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count__p2m_20aae0e7_47ce_430e_848b_f31970e65b06_a5
-- name    : WilliamsonShmoys.planar_drawing_face_count__p2m_20aae0e7_47ce_430e_848b_f31970e65b06_a5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T22:40:27.620726+00:00
-- url     : https://prove2.me/theorems/be1c2211-8706-4bdd-9db7-c51e2e4e9e09
-- title:
--   Euler equation and face incidences for a connected planar drawing
-- statement:
--   For a finite connected simple graph with at least three vertices and a crossing-free drawing, there is a natural face count satisfying Euler’s equation and the bound that the total facial boundary incidences are at least three per face.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_face_count__p2m_20aae0e7_47ce_430e_848b_f31970e65b06_a5 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hconn : K.Connected) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) : ∃ F : ℕ, K.edgeSet.ncard + 2 = Fintype.card V + F ∧ 3 * F ≤ 2 * K.edgeSet.ncard := by sorry
