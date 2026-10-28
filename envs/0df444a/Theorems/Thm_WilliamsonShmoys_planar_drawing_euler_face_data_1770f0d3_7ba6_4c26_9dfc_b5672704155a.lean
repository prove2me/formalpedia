-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_data_1770f0d3_7ba6_4c26_9dfc_b5672704155a
-- name    : WilliamsonShmoys.planar_drawing_euler_face_data_1770f0d3_7ba6_4c26_9dfc_b5672704155a
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T17:54:41.769495+00:00
-- url     : https://prove2.me/theorems/47870a7b-cca6-4de2-8960-61ca392c7e1a
-- title:
--   Euler face data from a planar drawing
-- statement:
--   A connected finite simple graph with at least three vertices and the supplied crossing-free drawing has a face count satisfying Euler’s equation and the total boundary-length bound. The independent route is to form the planar embedding from the given arcs, apply Euler’s formula, and count edge incidences along face boundaries; the lower bound on vertices and simplicity ensure each face boundary has length at least three, including when bridges make a face boundary repeat edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_euler_face_data_1770f0d3_7ba6_4c26_9dfc_b5672704155a {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hconn : K.Connected) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) : ∃ F : ℕ, Fintype.card V + F = K.edgeSet.ncard + 2 ∧ 3 * F ≤ 2 * K.edgeSet.ncard := by sorry
