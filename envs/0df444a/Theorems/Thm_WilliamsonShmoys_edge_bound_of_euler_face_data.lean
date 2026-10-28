-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_of_euler_face_data
-- name    : WilliamsonShmoys.edge_bound_of_euler_face_data
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T14:57:47.233068+00:00
-- url     : https://prove2.me/theorems/52fe484a-bdcf-4fc3-a9db-08bb62d06322
-- title:
--   Edge bound from Euler count and facial incidence
-- statement:
--   Natural vertex, edge, and face counts satisfying Euler’s relation and the facial incidence inequality obey the planar edge bound when there are at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edge_bound_of_euler_face_data (v e f : ℕ) (hEuler : v + f = e + 2) (hFaceDegrees : 3 * f <= 2 * e) (hv : 3 <= v) : e <= 3 * v - 6 := by sorry
