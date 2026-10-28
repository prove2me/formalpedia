-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_data
-- name    : WilliamsonShmoys.planar_drawing_face_data
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T00:44:06.998624+00:00
-- url     : https://prove2.me/theorems/6f4dc381-9904-4b9e-830f-ee684de45ddf
-- title:
--   Facial boundary lengths and Euler count
-- statement:
--   A connected simple graph with a crossing-free drawing and at least three vertices has facial boundary walks whose lengths are at least three, sum to twice the edge count, and whose number satisfies Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_face_data
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ m : ℕ, Fintype.card V + m = K.edgeSet.ncard + 2 ∧
      ∃ degree : Fin m → ℕ,
        (∑ i : Fin m, degree i) = 2 * K.edgeSet.ncard ∧
        ∀ i, 3 ≤ degree i := by sorry
