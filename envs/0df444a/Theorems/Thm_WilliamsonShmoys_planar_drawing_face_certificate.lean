-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_certificate
-- name    : WilliamsonShmoys.planar_drawing_face_certificate
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T09:17:52.990948+00:00
-- url     : https://prove2.me/theorems/b23a144d-0911-4865-bb2c-ca46dacec11c
-- title:
--   Extract face data from a connected planar drawing
-- statement:
--   A connected simple graph with at least three vertices and the supplied crossing-free drawing has finitely many faces whose degrees satisfy Euler’s equation, total incidence two per edge, and degree at least three. A concrete proof route extracts the rotation system and face permutation of the plane drawing, then proves Euler’s formula and the incidence properties.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_face_certificate
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    ∃ (m : Nat) (degree : Fin m → ℤ),
      (Fintype.card V : ℤ) - (K.edgeSet.ncard : ℤ) + m = 2 ∧
      (∑ f : Fin m, degree f) = 2 * (K.edgeSet.ncard : ℤ) ∧
      (∀ f, 3 ≤ degree f) := by sorry
