-- Prove2me | Theorems.Thm_WilliamsonShmoys_euler_face_count_bound_arithmetic
-- name    : WilliamsonShmoys.euler_face_count_bound_arithmetic
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:42:43.082668+00:00
-- url     : https://prove2.me/theorems/7652704f-e73b-4e1b-a520-440e436e0282
-- title:
--   Derive the planar edge bound from face counts
-- statement:
--   If the edge, vertex, and face counts satisfy Euler’s formula and three times the face count is at most twice the edge count, then the planar edge bound follows.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.euler_face_count_bound_arithmetic
    (m n f : ℕ)
    (hEuler : m + 2 = n + f)
    (hFaces : 3 * f ≤ 2 * m) :
    m + 6 ≤ 3 * n := by sorry
