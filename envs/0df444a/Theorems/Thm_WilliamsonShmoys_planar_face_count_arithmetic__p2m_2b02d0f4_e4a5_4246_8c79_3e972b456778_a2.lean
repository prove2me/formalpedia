-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_face_count_arithmetic__p2m_2b02d0f4_e4a5_4246_8c79_3e972b456778_a2
-- name    : WilliamsonShmoys.planar_face_count_arithmetic__p2m_2b02d0f4_e4a5_4246_8c79_3e972b456778_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:54:28.745371+00:00
-- url     : https://prove2.me/theorems/e308c0c8-11a9-4513-a6a0-af85975c6922
-- title:
--   Edge count from Euler and triangular face counts
-- statement:
--   Combine Euler’s formula with the two face sides per edge and the total triangular face length to derive the natural-number edge count. The hypothesis n ≥ 3 ensures the subtraction in the conclusion is not truncated below zero.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_face_count_arithmetic__p2m_2b02d0f4_e4a5_4246_8c79_3e972b456778_a2
    {F : Type} [Fintype F]
    (n e : ℕ) (length : F → ℕ)
    (hn : 3 ≤ n)
    (hEuler : (n : ℤ) - (e : ℤ) + (Fintype.card F : ℤ) = 2)
    (hIncidence : (∑ f : F, (length f : ℤ)) = 2 * (e : ℤ))
    (hTriangular : (∑ f : F, (length f : ℤ)) = 3 * (Fintype.card F : ℤ)) :
    e = 3 * n - 6 := by sorry
