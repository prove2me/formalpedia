-- Prove2me | Theorems.Thm_WilliamsonShmoys_euler_face_edge_arithmetic__p2m_8e79e615_ce68_4197_8611_7fa93173a04e_a2
-- name    : WilliamsonShmoys.euler_face_edge_arithmetic__p2m_8e79e615_ce68_4197_8611_7fa93173a04e_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:17:12.19275+00:00
-- url     : https://prove2.me/theorems/137dd1cd-c7ff-4d8d-859a-a07acf7e3dfb
-- title:
--   Euler face data imply the planar edge bound
-- statement:
--   Natural numbers representing vertices, edges, and faces satisfy the planar edge bound when Euler’s equation holds, the aggregate facial-boundary incidence is at least three per face, and there are at least three vertices. The lower bound on `n` preserves the natural-subtraction boundary.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.euler_face_edge_arithmetic__p2m_8e79e615_ce68_4197_8611_7fa93173a04e_a2
    (n e f : ℕ)
    (hn : 3 ≤ n)
    (heuler : n + f = e + 2)
    (hfaces : 3 * f ≤ 2 * e) :
    e ≤ 3 * n - 6 := by sorry
