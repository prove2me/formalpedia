-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_face_count_arithmetic__p2m_849752b4_78ce_4d07_98c6_f3ea971ec2cd_a2
-- name    : WilliamsonShmoys.planar_face_count_arithmetic__p2m_849752b4_78ce_4d07_98c6_f3ea971ec2cd_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:36:01.808167+00:00
-- url     : https://prove2.me/theorems/54ef5c17-3abe-4b8f-b50d-c5f70036e396
-- title:
--   Edge bound from Euler and face counts
-- statement:
--   For natural numbers n, m, and f, if n is at least three, n − m + f = 2 over the integers, and 3f ≤ 2m, then m ≤ 3n − 6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_face_count_arithmetic__p2m_849752b4_78ce_4d07_98c6_f3ea971ec2cd_a2
    (n m f : ℕ)
    (hn : 3 ≤ n)
    (hEuler : (n : ℤ) - (m : ℤ) + (f : ℤ) = 2)
    (hFaces : 3 * f ≤ 2 * m) :
    m ≤ 3 * n - 6 := by sorry
