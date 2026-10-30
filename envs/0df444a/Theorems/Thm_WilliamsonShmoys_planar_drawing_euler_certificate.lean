-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_certificate
-- name    : WilliamsonShmoys.planar_drawing_euler_certificate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:12:25.108064+00:00
-- url     : https://prove2.me/theorems/7e884632-995f-4722-8cfd-6873d9d546c4
-- title:
--   Euler and face-incidence certificate for a planar drawing
-- statement:
--   A connected graph with at least three vertices and the supplied crossing-free arc drawing has a face count satisfying Euler’s formula and the face-incidence lower bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_euler_certificate
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    ∃ f : Nat,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * K.edgeSet.ncard := by
  sorry
