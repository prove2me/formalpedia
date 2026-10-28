-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_edge_count_from_face_equations
-- name    : WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_edge_count_from_face_equations
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T10:11:08.871433+00:00
-- url     : https://prove2.me/theorems/2297fec5-9dce-4364-a582-2d041a08d253
-- title:
--   Edge count from Euler and face incidence
-- statement:
--   For natural numbers satisfying Euler’s equation and the triangular-face incidence equation, at least three vertices imply the edge count is 3n − 6. This isolates the arithmetic from the topological argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_edge_count_from_face_equations
    (n m f : ℕ) (hCard : 3 ≤ n)
    (hEuler : n + f = m + 2)
    (hIncidence : 3 * f = 2 * m) :
    m = 3 * n - 6 := by sorry
