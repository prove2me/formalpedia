-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_face_count_arithmetic
-- name    : WilliamsonShmoys.planar_face_count_arithmetic
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:09:29.278484+00:00
-- url     : https://prove2.me/theorems/ccd46cd4-cc6f-40d4-b32f-bc13593bf90f
-- title:
--   Derive the edge bound from Euler face counts
-- statement:
--   Euler’s count and the perimeter inequality imply the desired edge bound. Multiply the Euler equality by three, combine it with the perimeter inequality, and use n ≥ 3 to discharge the natural-number subtraction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_face_count_arithmetic
    (n m f : ℕ)
    (hn : 3 ≤ n)
    (hEuler : n + f = m + 2)
    (hPerimeter : 3 * f ≤ 2 * m) :
    m ≤ 3 * n - 6 := by sorry
