-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_face_count_arithmetic_bound__p2m_cfd012c7_8a6d_483e_9797_29a733a7d0a7_a1
-- name    : WilliamsonShmoys.planar_face_count_arithmetic_bound__p2m_cfd012c7_8a6d_483e_9797_29a733a7d0a7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:32:46.403108+00:00
-- url     : https://prove2.me/theorems/070ae7a0-acfa-479b-8ab4-cba976707249
-- title:
--   Arithmetic consequence of planar face counts
-- statement:
--   If natural numbers `n` and `m` and an integer `f` satisfy Euler’s face-count equation and the face-incidence lower bound, then `m ≤ 3n − 6`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.planar_face_count_arithmetic_bound__p2m_cfd012c7_8a6d_483e_9797_29a733a7d0a7_a1 (n m : ℕ) (hn : 3 ≤ n) (f : ℤ) (heuler : (n : ℤ) - (m : ℤ) + f = 2) (hinc : 3 * f ≤ 2 * (m : ℤ)) : m ≤ 3 * n - 6 := by sorry
