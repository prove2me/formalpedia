-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_face_data_edge_bound__p2m_7d4137c4_15dc_451a_ba6d_47dc1f35dd68_a1
-- name    : WilliamsonShmoys.planar_face_data_edge_bound__p2m_7d4137c4_15dc_451a_ba6d_47dc1f35dd68_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:14:05.857122+00:00
-- url     : https://prove2.me/theorems/375a9942-9730-4dc6-8efb-884f4d02d888
-- title:
--   Edge bound from Euler and face lengths
-- statement:
--   If a finite face-boundary list has total length twice the edge count, each face length is at least three, and Euler’s equation holds, then the edge count is at most three times the vertex count minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_face_data_edge_bound__p2m_7d4137c4_15dc_451a_ba6d_47dc1f35dd68_a1
    (n m f : ℕ) (boundary : Fin f → ℕ)
    (hn : 3 ≤ n)
    (heuler : n + f = m + 2)
    (htotal : (∑ i : Fin f, boundary i) = 2 * m)
    (hface : ∀ i, 3 ≤ boundary i) :
    m ≤ 3 * n - 6 := by sorry
