-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_count_arithmetic__p2m_57c3e2f0_3143_4ad3_84d0_92c0d48df09b_a2
-- name    : WilliamsonShmoys.face_count_arithmetic__p2m_57c3e2f0_3143_4ad3_84d0_92c0d48df09b_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:27:33.257038+00:00
-- url     : https://prove2.me/theorems/5374c3a3-e6b1-434b-8eeb-7f8c1b2e0edb
-- title:
--   Euler face-count arithmetic bound
-- statement:
--   If a connected plane graph’s vertex, edge, and face counts satisfy Euler’s relation and every face contributes at least three boundary incidences, then its edge count is at most three times its vertex count minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.face_count_arithmetic__p2m_57c3e2f0_3143_4ad3_84d0_92c0d48df09b_a2
    (n m f : Nat) (hn : 3 ≤ n)
    (hEuler : n + f = m + 2)
    (hFaces : 3 * f ≤ 2 * m) :
    m ≤ 3 * n - 6 := by sorry
