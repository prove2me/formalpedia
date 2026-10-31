-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_count_arithmetic__p2m_e194ab00_41b0_4b4f_af08_d9da373e3f16_a1
-- name    : WilliamsonShmoys.face_count_arithmetic__p2m_e194ab00_41b0_4b4f_af08_d9da373e3f16_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:50:09.29081+00:00
-- url     : https://prove2.me/theorems/ee4652ec-acde-4835-9306-3d762fd06947
-- title:
--   Arithmetic construction of the face count
-- statement:
--   For natural numbers n and m satisfying 3n = m + 6, there is a natural number f satisfying n + f = m + 2 and 3f = 2m.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.face_count_arithmetic__p2m_e194ab00_41b0_4b4f_af08_d9da373e3f16_a1
    (n m : ℕ)
    (h : 3 * n = m + 6) :
    ∃ f : ℕ, n + f = m + 2 ∧ 3 * f = 2 * m := by sorry
