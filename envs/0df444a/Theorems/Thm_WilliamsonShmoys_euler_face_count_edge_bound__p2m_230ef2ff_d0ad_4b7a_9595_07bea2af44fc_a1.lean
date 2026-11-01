-- Prove2me | Theorems.Thm_WilliamsonShmoys_euler_face_count_edge_bound__p2m_230ef2ff_d0ad_4b7a_9595_07bea2af44fc_a1
-- name    : WilliamsonShmoys.euler_face_count_edge_bound__p2m_230ef2ff_d0ad_4b7a_9595_07bea2af44fc_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:01:55.237033+00:00
-- url     : https://prove2.me/theorems/d1cc4e0f-9621-422b-9794-31b056b3db1a
-- title:
--   Euler face counts imply the planar edge bound
-- statement:
--   If a finite plane map satisfies Euler’s vertex-face-edge equation, its face boundary lengths sum to twice its edge count, and every face boundary length is at least three, then its edge count plus six is at most three times its vertex count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem WilliamsonShmoys.euler_face_count_edge_bound__p2m_230ef2ff_d0ad_4b7a_9595_07bea2af44fc_a1 {v e f : ℕ} (ell : Fin f → ℕ) (hEuler : v + f = e + 2) (hsum : (∑ i : Fin f, ell i) = 2 * e) (hlen : ∀ i, 3 ≤ ell i) : e + 6 ≤ 3 * v := by sorry
