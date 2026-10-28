-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_face_count_data
-- name    : WilliamsonShmoys.planar_edge_bound_from_face_count_data
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T09:43:40.730933+00:00
-- url     : https://prove2.me/theorems/979617cc-762a-4a31-8bcd-a5d1cac5162b
-- title:
--   Planar edge bound from face-count data
-- statement:
--   Derive the planar edge bound from Euler’s equation and the two boundary-incidence inequalities. This isolates only natural-number linear arithmetic and can be proved directly with `omega`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_bound_from_face_count_data
    (n m f b : ℕ)
    (hEuler : n + f = m + 2)
    (hBoundary : b = 2 * m)
    (hIncidences : 3 * f ≤ b) :
    m + 6 ≤ 3 * n := by sorry
