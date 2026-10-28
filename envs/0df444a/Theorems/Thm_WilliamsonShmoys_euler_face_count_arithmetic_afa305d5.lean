-- Prove2me | Theorems.Thm_WilliamsonShmoys_euler_face_count_arithmetic_afa305d5
-- name    : WilliamsonShmoys.euler_face_count_arithmetic_afa305d5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T13:24:27.22879+00:00
-- url     : https://prove2.me/theorems/fd4ecd62-7d35-480b-a454-0909e15435fe
-- title:
--   Edge bound from Euler and triangular-face counts
-- statement:
--   For natural numbers satisfying Euler’s equation and the triangular face-incidence equation, the claimed lower edge bound follows by natural-number linear arithmetic. This removes the counting manipulation from the geometric child.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.euler_face_count_arithmetic_afa305d5
    (n m f : Nat)
    (hEuler : n + f = m + 2)
    (hIncidence : 2 * m = 3 * f) :
    3 * n <= m + 6 := by sorry
