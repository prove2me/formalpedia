-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_count_arithmetic__p2m_dbcd4af9_e055_47f7_910a_a01842a93823_a2
-- name    : WilliamsonShmoys.face_count_arithmetic__p2m_dbcd4af9_e055_47f7_910a_a01842a93823_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:42:09.484637+00:00
-- url     : https://prove2.me/theorems/2319c846-264e-447a-8a2a-029cfdc2afa5
-- title:
--   Planar face-count arithmetic
-- statement:
--   If natural numbers n, m, and f satisfy the plane Euler equation n+f=m+2 and the face-incidence bound 3f≤2m, then m+6≤3n.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.face_count_arithmetic__p2m_dbcd4af9_e055_47f7_910a_a01842a93823_a2
    (n m f : ℕ)
    (hEuler : n + f = m + 2)
    (hFaceLength : 3 * f <= 2 * m) :
    m + 6 <= 3 * n := by sorry
