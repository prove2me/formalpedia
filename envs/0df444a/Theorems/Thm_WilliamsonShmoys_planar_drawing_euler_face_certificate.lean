-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_certificate
-- name    : WilliamsonShmoys.planar_drawing_euler_face_certificate
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T00:49:45.906983+00:00
-- url     : https://prove2.me/theorems/9b8cd460-1af4-4f95-907b-c227227a2f0d
-- title:
--   Triangulated planar supergraph Euler certificate
-- statement:
--   Any finite simple graph on at least three vertices with the supplied crossing-free drawing has a spanning simple supergraph whose connected triangulated planar embedding yields Euler’s vertex-edge-face equation and the face-incidence bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_euler_face_certificate
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ (K : SimpleGraph V) (f : ℕ),
      H ≤ K ∧
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * K.edgeSet.ncard := by sorry
