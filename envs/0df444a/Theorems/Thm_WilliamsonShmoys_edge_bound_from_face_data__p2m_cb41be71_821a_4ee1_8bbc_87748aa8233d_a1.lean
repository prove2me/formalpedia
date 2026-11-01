-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_from_face_data__p2m_cb41be71_821a_4ee1_8bbc_87748aa8233d_a1
-- name    : WilliamsonShmoys.edge_bound_from_face_data__p2m_cb41be71_821a_4ee1_8bbc_87748aa8233d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:02:33.0302+00:00
-- url     : https://prove2.me/theorems/9d21cf04-ef64-4020-9f8d-b448860f3a5c
-- title:
--   Derive the planar edge bound from face data
-- statement:
--   Natural-number vertex, edge, and face counts satisfying Euler’s equation and the total face-boundary inequality satisfy the planar edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edge_bound_from_face_data__p2m_cb41be71_821a_4ee1_8bbc_87748aa8233d_a1 (v e f : ℕ) (heuler : v + f = e + 2) (hfaces : 3 * f <= 2 * e) : e + 6 <= 3 * v := by sorry
