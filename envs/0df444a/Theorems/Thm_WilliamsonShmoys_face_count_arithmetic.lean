-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_count_arithmetic
-- name    : WilliamsonShmoys.face_count_arithmetic
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T02:25:20.457519+00:00
-- url     : https://prove2.me/theorems/e92d44f8-ccac-4c52-a916-031ca34cfef9
-- title:
--   Derive the edge count from Euler and face incidences
-- statement:
--   For natural numbers n, e, and f, Euler’s equation n + f = e + 2 together with the triangular-face incidence equation 3f = 2e implies e + 6 = 3n. This is pure arithmetic and has no extra boundary hypotheses.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.face_count_arithmetic
    (n e f : ℕ)
    (hEuler : n + f = e + 2)
    (hFaces : 3 * f = 2 * e) :
    e + 6 = 3 * n := by sorry
