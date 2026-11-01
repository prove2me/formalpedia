-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_face_count_arithmetic__p2m_62c40d5f_afd7_4bfc_ad24_9691a3287af2_a2
-- name    : WilliamsonShmoys.planar_face_count_arithmetic__p2m_62c40d5f_afd7_4bfc_ad24_9691a3287af2_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:57:33.324197+00:00
-- url     : https://prove2.me/theorems/2ee1100d-2cd6-4f44-946b-3d287aed348b
-- title:
--   Edge bound from Euler and face-degree counts
-- statement:
--   For natural numbers counting vertices, edges, and faces, Euler’s relation together with the lower bound on total face degrees implies the planar edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_face_count_arithmetic__p2m_62c40d5f_afd7_4bfc_ad24_9691a3287af2_a2
    (n m f : ℕ) (hn : 3 ≤ n) (heuler : n + f = m + 2)
    (hdegree : 3 * f ≤ 2 * m) :
    m + 6 ≤ 3 * n := by
  sorry
