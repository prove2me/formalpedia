-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_face_bound_from_euler_and_edge_bound__p2m_7b82f13f_4972_4c18_a653_c5d0801ea028_a2
-- name    : WilliamsonShmoys.planar_face_bound_from_euler_and_edge_bound__p2m_7b82f13f_4972_4c18_a653_c5d0801ea028_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:32:37.699935+00:00
-- url     : https://prove2.me/theorems/de17739c-38b5-4540-87d8-466e7d3a71de
-- title:
--   Facial bound from Euler’s identity and the planar edge bound
-- statement:
--   For natural numbers E, V, and f, if E + 2 = V + f and E + 6 ≤ 3V, then 3f ≤ 2E.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_face_bound_from_euler_and_edge_bound__p2m_7b82f13f_4972_4c18_a653_c5d0801ea028_a2
    (E V f : Nat)
    (heuler : E + 2 = V + f)
    (hbound : E + 6 <= 3 * V) :
    3 * f <= 2 * E := by
  sorry
