-- Prove2me | Theorems.Thm_maximal_planar_edge_count_euler_arithmetic__p2m_5372b848_7d0c_4e54_bcd1_c004f9c1519b_a3
-- name    : maximal_planar_edge_count_euler_arithmetic__p2m_5372b848_7d0c_4e54_bcd1_c004f9c1519b_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:52:19.853962+00:00
-- url     : https://prove2.me/theorems/cfd0f306-e0d3-4a5c-80a8-b497ef5fa3e3
-- title:
--   Edge bound from Euler and triangular-face counts
-- statement:
--   The Euler and triangular-face equations imply the planar edge-count bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem maximal_planar_edge_count_euler_arithmetic__p2m_5372b848_7d0c_4e54_bcd1_c004f9c1519b_a3 (n e f : ℕ) (hEuler : n + f = e + 2) (hFaces : 3 * f = 2 * e) : 3 * n ≤ e + 6 := by sorry
