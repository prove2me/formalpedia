-- Prove2me | Theorems.Thm_WilliamsonShmoys_euler_face_count_implies_edge_bound
-- name    : WilliamsonShmoys.euler_face_count_implies_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:57:07.869993+00:00
-- url     : https://prove2.me/theorems/d252244c-0858-4f1e-bcd8-ea372bf38189
-- title:
--   Derive the planar edge bound from face-count inequalities
-- statement:
--   Natural numbers satisfying the Euler face-count equation and aggregate face-boundary inequality satisfy the planar edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.euler_face_count_implies_edge_bound
    (n m f : ℕ)
    (hEuler : n + f = m + 2)
    (hFaces : 3 * f ≤ 2 * m) :
    m + 6 ≤ 3 * n := by sorry
