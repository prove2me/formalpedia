-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_from_euler_and_triangular_faces
-- name    : WilliamsonShmoys.edge_count_from_euler_and_triangular_faces
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:29:47.346838+00:00
-- url     : https://prove2.me/theorems/dc224950-dbe7-4f23-8f85-b7917b403aa5
-- title:
--   Edge count from Euler and triangular face counts
-- statement:
--   For natural numbers n, m, and f, Euler’s relation and the triangular face-edge incidence relation imply the planar triangulation edge count when n is at least three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_from_euler_and_triangular_faces
    (n m f : Nat)
    (hLarge : 3 ≤ n)
    (hEuler : n + f = m + 2)
    (hTriangular : 2 * m = 3 * f) :
    m = 3 * n - 6 := by sorry
