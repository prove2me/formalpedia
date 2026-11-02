-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_extension_of_finite_preorder__p2m_7fc18aad_d07a_49bb_b01c_abff1eddf2b3_a2
-- name    : WilliamsonShmoys.exists_maximal_extension_of_finite_preorder__p2m_7fc18aad_d07a_49bb_b01c_abff1eddf2b3_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:22:39.709106+00:00
-- url     : https://prove2.me/theorems/67cb0e08-f0b3-4a2f-8d0e-c954f6fa6639
-- title:
--   Maximal extension in a finite preorder
-- statement:
--   In a finite preorder, every predicate-satisfying element has a predicate-satisfying extension that is maximal among predicate-satisfying elements above it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_extension_of_finite_preorder__p2m_7fc18aad_d07a_49bb_b01c_abff1eddf2b3_a2 {α : Type} [Finite α] [Preorder α] (x : α) (Q : α → Prop) (hx : Q x) : ∃ y : α, Q y ∧ x ≤ y ∧ ∀ z : α, Q z → y ≤ z → z ≤ y := by sorry
