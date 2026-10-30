-- Prove2me | Theorems.Thm_WilliamsonShmoys_has_euler_face_count_bound
-- name    : WilliamsonShmoys.has_euler_face_count_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T20:19:00.694872+00:00
-- url     : https://prove2.me/theorems/bbcc6704-0440-4d8a-8be6-bf0d05d75f7c
-- title:
--   A planar drawing has an Euler face count
-- statement:
--   For a connected simple graph with at least three vertices and the supplied crossing-free drawing, there is a finite face count satisfying Euler’s equation and the inequality obtained by counting each edge twice and each face boundary with length at least three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.has_euler_face_count_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * K.edgeSet.ncard := by sorry
