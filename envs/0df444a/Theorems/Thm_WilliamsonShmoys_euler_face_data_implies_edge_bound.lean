-- Prove2me | Theorems.Thm_WilliamsonShmoys_euler_face_data_implies_edge_bound
-- name    : WilliamsonShmoys.euler_face_data_implies_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:05:17.572087+00:00
-- url     : https://prove2.me/theorems/ad7a327c-b9cd-475b-942c-05588fe252fb
-- title:
--   Euler and face-degree data imply the planar edge bound
-- statement:
--   For natural-number vertex, edge, face, and component counts, the stated Euler relation, positive component count, and aggregate face-degree bound imply the claimed edge bound. This is a finite arithmetic step independent of the drawing construction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.euler_face_data_implies_edge_bound
    {n m f c : ℕ}
    (hn : 3 ≤ n)
    (hm : 2 ≤ m)
    (heuler : n + f = m + c + 1)
    (hc : 1 ≤ c)
    (hdegree : 3 * f ≤ 2 * m) :
    m + 6 ≤ 3 * n := by sorry
