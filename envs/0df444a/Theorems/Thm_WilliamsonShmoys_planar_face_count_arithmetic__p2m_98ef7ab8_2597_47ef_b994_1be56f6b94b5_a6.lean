-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_face_count_arithmetic__p2m_98ef7ab8_2597_47ef_b994_1be56f6b94b5_a6
-- name    : WilliamsonShmoys.planar_face_count_arithmetic__p2m_98ef7ab8_2597_47ef_b994_1be56f6b94b5_a6
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T20:59:49.267755+00:00
-- url     : https://prove2.me/theorems/bbccfd9f-df0c-4226-829a-7091465987ce
-- title:
--   Edge bound from planar face counts
-- statement:
--   Derive the integer edge bound from a natural-number face count satisfying Euler’s equation and the face-boundary side-count inequality, retaining the hypothesis that the vertex count is at least three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_face_count_arithmetic__p2m_98ef7ab8_2597_47ef_b994_1be56f6b94b5_a6 {n m : Nat} (hdata : ∃ f : Nat, n + f = m + 2 ∧ 3 * f ≤ 2 * m) (hn : 3 ≤ n) : (m : Int) ≤ 3 * (n : Int) - 6 := by sorry
