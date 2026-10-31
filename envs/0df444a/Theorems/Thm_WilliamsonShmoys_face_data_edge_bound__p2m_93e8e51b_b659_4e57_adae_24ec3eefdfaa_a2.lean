-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_data_edge_bound__p2m_93e8e51b_b659_4e57_adae_24ec3eefdfaa_a2
-- name    : WilliamsonShmoys.face_data_edge_bound__p2m_93e8e51b_b659_4e57_adae_24ec3eefdfaa_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:34:52.32498+00:00
-- url     : https://prove2.me/theorems/007e2912-9d46-4eed-bed6-d86da4a573a9
-- title:
--   Euler face data gives the planar edge bound
-- statement:
--   If natural numbers n, m, and k satisfy Euler’s equation, and k boundary lengths sum to 2m with each at least three, then m + 6 ≤ 3n. Sum the lower bounds to obtain 3k ≤ 2m and combine this with Euler’s equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.face_data_edge_bound__p2m_93e8e51b_b659_4e57_adae_24ec3eefdfaa_a2
    (n m k : ℕ) (boundary : Fin k → ℕ)
    (hEuler : n + k = m + 2)
    (hBoundarySum : (∑ i, boundary i) = 2 * m)
    (hFaceLength : ∀ i, 3 ≤ boundary i) :
    m + 6 ≤ 3 * n := by sorry
