-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_count_edge_bound__p2m_ab4fcf06_6052_4762_83f6_1c588acec272_a1
-- name    : WilliamsonShmoys.face_count_edge_bound__p2m_ab4fcf06_6052_4762_83f6_1c588acec272_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:23:24.706335+00:00
-- url     : https://prove2.me/theorems/c0b0386d-b87f-4410-b174-b01cf06da3ef
-- title:
--   Euler face counting implies the planar edge bound
-- statement:
--   For finite face data with total boundary length twice the edge count, all face lengths at least three, and Euler's equation, the edge count is at most three times the vertex count minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.face_count_edge_bound__p2m_ab4fcf06_6052_4762_83f6_1c588acec272_a1 (v e : ℕ) (F : Type) [Fintype F] (length : F → ℕ) (hv : 3 ≤ v) (hsum : (∑ f : F, length f) = 2 * e) (hlen : ∀ f : F, 3 ≤ length f) (heuler : v + Fintype.card F = e + 2) : e + 6 ≤ 3 * v := by sorry
