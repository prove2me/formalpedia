-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_count_arithmetic__p2m_9667c397_02c4_4afb_ad3c_3d8252f0b79d_a1
-- name    : WilliamsonShmoys.face_count_arithmetic__p2m_9667c397_02c4_4afb_ad3c_3d8252f0b79d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:07:47.277466+00:00
-- url     : https://prove2.me/theorems/e069bf77-12da-4a1e-a6ce-0885171ce498
-- title:
--   Triangular face count implies the planar edge bound
-- statement:
--   If a finite collection of triangular faces satisfies Euler’s equation and each edge is counted twice among face boundaries, then the vertex and edge counts satisfy the planar lower bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.face_count_arithmetic__p2m_9667c397_02c4_4afb_ad3c_3d8252f0b79d_a1
    (n m f : Nat) (len : Fin f -> Nat)
    (heuler : n + f = m + 2)
    (hinc : Finset.univ.sum (fun i : Fin f => len i) = 2 * m)
    (htri : forall i : Fin f, len i = 3) :
    3 * n <= m + 6 := by
  sorry
