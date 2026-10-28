-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_boundary_bound__p2m_47870a7b_cca6_4de2_8960_61ca392c7e1a_a1
-- name    : WilliamsonShmoys.planar_drawing_face_boundary_bound__p2m_47870a7b_cca6_4de2_8960_61ca392c7e1a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:25:19.434013+00:00
-- url     : https://prove2.me/theorems/04f4db05-702a-494d-b920-fe439899ceaa
-- title:
--   Boundary incidence bound for planar faces
-- statement:
--   For a finite connected simple graph with at least three vertices and the supplied planar drawing, any natural face count satisfying Euler's equation is bounded by the total number of directed edge incidences: three times the face count is at most twice the edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_face_boundary_bound__p2m_47870a7b_cca6_4de2_8960_61ca392c7e1a_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hconn : K.Connected) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) (F : ℕ) (hEuler : Fintype.card V + F = K.edgeSet.ncard + 2) : 3 * F ≤ 2 * K.edgeSet.ncard := by sorry
