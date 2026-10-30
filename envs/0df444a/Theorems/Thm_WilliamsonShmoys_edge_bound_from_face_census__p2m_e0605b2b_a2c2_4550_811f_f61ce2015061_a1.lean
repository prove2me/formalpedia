-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_from_face_census__p2m_e0605b2b_a2c2_4550_811f_f61ce2015061_a1
-- name    : WilliamsonShmoys.edge_bound_from_face_census__p2m_e0605b2b_a2c2_4550_811f_f61ce2015061_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:58:46.702641+00:00
-- url     : https://prove2.me/theorems/e8dd6ccd-3570-4c8f-b8ff-a491aef470af
-- title:
--   Derive the planar edge bound from the face census
-- statement:
--   If natural numbers for vertices, edges, and faces satisfy Euler’s equation and the planar face-incidence inequality, then the edge count is at most three times the vertex count minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.edge_bound_from_face_census__p2m_e0605b2b_a2c2_4550_811f_f61ce2015061_a1
    (n m f : ℕ)
    (heuler : n + f = m + 2)
    (hfaces : 3 * f <= 2 * m) :
    m + 6 <= 3 * n := by sorry
