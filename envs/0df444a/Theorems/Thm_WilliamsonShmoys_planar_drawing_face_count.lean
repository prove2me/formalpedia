-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count
-- name    : WilliamsonShmoys.planar_drawing_face_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T20:33:16.619496+00:00
-- url     : https://prove2.me/theorems/60c853e0-3c19-4770-b067-4a315e6d80ae
-- title:
--   Euler and face incidence bounds from a planar drawing
-- statement:
--   For a connected simple graph with at least three vertices, a crossing-free drawing induces a finite face count satisfying Euler’s equation and the aggregate face-boundary incidence inequality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_face_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      K.edgeSet.ncard + 2 = Fintype.card V + f ∧
      3 * f ≤ 2 * K.edgeSet.ncard := by sorry
