-- Prove2me | Theorems.Thm_WilliamsonShmoys_euler_data_edge_bound__p2m_b0556792_8fbb_42b1_83f9_e49450aba15a_a2
-- name    : WilliamsonShmoys.euler_data_edge_bound__p2m_b0556792_8fbb_42b1_83f9_e49450aba15a_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:27:13.789858+00:00
-- url     : https://prove2.me/theorems/eaeab1a6-167b-441a-ada5-9fa50f71f82b
-- title:
--   Edge bound from Euler and face data
-- statement:
--   For natural-number vertex, edge, face, and total-boundary counts, Euler's equation, two sides per edge, and the total face-length lower bound imply the planar edge bound. This child removes the arithmetic from the parent and has an independent proof by substituting the equalities and using natural-number linear arithmetic. The hypothesis n ≥ 3 is retained from the drawing argument, although the displayed arithmetic implication itself follows without it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.euler_data_edge_bound__p2m_b0556792_8fbb_42b1_83f9_e49450aba15a_a2
    (n e f l : ℕ)
    (hn : 3 ≤ n)
    (hEuler : n + f = e + 2)
    (hSides : l = 2 * e)
    (hFaces : 3 * f ≤ l) :
    e + 6 ≤ 3 * n := by sorry
