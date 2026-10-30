-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_boundary_list_bound__p2m_189aab1a_280b_4ab3_961b_1c0b2454cb23_a4
-- name    : WilliamsonShmoys.face_boundary_list_bound__p2m_189aab1a_280b_4ab3_961b_1c0b2454cb23_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T19:01:41.568614+00:00
-- url     : https://prove2.me/theorems/7aa19ac2-cf0a-4470-bcac-218d9bedd9cc
-- title:
--   Lower bound on the sum of face-boundary lengths
-- statement:
--   For a finite list of natural numbers whose entries are all at least three, three times the list length is at most the sum, including when the list is empty.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.face_boundary_list_bound__p2m_189aab1a_280b_4ab3_961b_1c0b2454cb23_a4 (lengths : List ℕ)
    (hLower : ∀ x ∈ lengths, 3 ≤ x) :
    3 * lengths.length ≤ lengths.sum := by sorry
