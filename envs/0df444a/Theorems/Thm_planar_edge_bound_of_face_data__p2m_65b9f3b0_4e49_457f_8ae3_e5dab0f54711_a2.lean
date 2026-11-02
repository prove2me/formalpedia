-- Prove2me | Theorems.Thm_planar_edge_bound_of_face_data__p2m_65b9f3b0_4e49_457f_8ae3_e5dab0f54711_a2
-- name    : planar_edge_bound_of_face_data__p2m_65b9f3b0_4e49_457f_8ae3_e5dab0f54711_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:11:42.874997+00:00
-- url     : https://prove2.me/theorems/62b1a296-3dbc-4bfa-889b-f8902e044139
-- title:
--   Edge bound from Euler and face lengths
-- statement:
--   Natural numbers satisfying n ≥ 3, n + f = m + 2, and 3f ≤ 2m satisfy m ≤ 3n − 6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem planar_edge_bound_of_face_data__p2m_65b9f3b0_4e49_457f_8ae3_e5dab0f54711_a2
    (n f m : Nat) (hn : 3 ≤ n)
    (heuler : n + f = m + 2)
    (hfaces : 3 * f ≤ 2 * m) :
    m ≤ 3 * n - 6 := by sorry
