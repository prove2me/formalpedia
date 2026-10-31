-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_from_face_count__p2m_84c43119_f87e_4738_abb0_0796ef4e5b94_a2
-- name    : WilliamsonShmoys.edge_bound_from_face_count__p2m_84c43119_f87e_4738_abb0_0796ef4e5b94_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:49:59.933259+00:00
-- url     : https://prove2.me/theorems/d4f8d387-9206-45b9-aad3-c465e5520f51
-- title:
--   Derive the planar edge bound from face counts
-- statement:
--   For natural numbers with at least three vertices, Euler’s relation and the face-incidence inequalities imply the planar edge-count bound. Substitute the equations and inequalities to obtain `e + 6 ≤ 3*n`, then handle natural subtraction using `hCard`. The proof is elementary arithmetic, independently checkable with `omega`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.edge_bound_from_face_count__p2m_84c43119_f87e_4738_abb0_0796ef4e5b94_a2 (n e : Nat) (hCard : 3 ≤ n) (hCounts : ∃ F B : Nat, n + F = e + 2 ∧ B = 2 * e ∧ 3 * F ≤ B) : e ≤ 3 * n - 6 := by sorry
