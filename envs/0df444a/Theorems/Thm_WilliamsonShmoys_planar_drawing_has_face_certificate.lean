-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_face_certificate
-- name    : WilliamsonShmoys.planar_drawing_has_face_certificate
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T23:06:14.067027+00:00
-- url     : https://prove2.me/theorems/3078beb6-cc76-4300-9158-26716fca0733
-- title:
--   A planar drawing yields face-counting data
-- statement:
--   A connected graph with at least three vertices and a crossing-free drawing admits face counts whose boundary lengths satisfy Euler’s formula, sum to twice the edge count, and are each at least three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_face_certificate
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ (faceCount : ℕ) (boundaryLength : Fin faceCount → ℕ),
      Fintype.card V + faceCount = K.edgeSet.ncard + 2 ∧
      (∑ i : Fin faceCount, boundaryLength i) = 2 * K.edgeSet.ncard ∧
      ∀ i : Fin faceCount, 3 ≤ boundaryLength i := by sorry
