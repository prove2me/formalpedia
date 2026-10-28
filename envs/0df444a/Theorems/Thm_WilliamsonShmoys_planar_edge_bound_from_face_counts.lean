-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_face_counts
-- name    : WilliamsonShmoys.planar_edge_bound_from_face_counts
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T01:55:30.003325+00:00
-- url     : https://prove2.me/theorems/9aa861da-3da7-470d-a41e-1e4ab6692089
-- title:
--   Deriving the planar edge bound from face counts
-- statement:
--   For natural numbers n, e, and f, Euler’s relation and the face-edge incidence inequality imply the planar edge bound. This is a separate natural-number arithmetic step, provable by linear arithmetic.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.planar_edge_bound_from_face_counts
    (n e f : ℕ)
    (hEuler : n + f = e + 2)
    (hFaceIncidence : 3 * f ≤ 2 * e) :
    e + 6 ≤ 3 * n := by sorry
