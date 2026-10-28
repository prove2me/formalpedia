-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_face_count_arithmetic_282b0fbb
-- name    : WilliamsonShmoys.planar_face_count_arithmetic_282b0fbb
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T10:47:36.177594+00:00
-- url     : https://prove2.me/theorems/41e5ce1a-cab7-4954-a4ee-8471973f5f4b
-- title:
--   Edge bound from facial boundary lengths
-- statement:
--   If a finite list of facial boundary lengths satisfies Euler’s equation, sums to twice the edge count, and every entry is at least three, then a graph with at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_face_count_arithmetic_282b0fbb
    (n m : ℕ) (faces : List ℕ)
    (hCard : 3 <= n)
    (hEuler : (n : Int) - (m : Int) + (faces.length : Int) = 2)
    (hIncidence : faces.sum = 2 * m)
    (hFaceLength : ∀ f, f ∈ faces → 3 <= f) :
    (m : Int) <= 3 * (n : Int) - 6 := by sorry
