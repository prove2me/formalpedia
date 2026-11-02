-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_simpleGraph_supergraph_maximal__p2m_7fc18aad_d07a_49bb_b01c_abff1eddf2b3_a1
-- name    : WilliamsonShmoys.finite_simpleGraph_supergraph_maximal__p2m_7fc18aad_d07a_49bb_b01c_abff1eddf2b3_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:11:06.86549+00:00
-- url     : https://prove2.me/theorems/a806b62f-032f-47b9-a30c-43e2f2e16ccc
-- title:
--   Maximal extension in a finite preorder
-- statement:
--   In a finite preorder, every element satisfying a predicate has a predicate-satisfying extension that is maximal among predicate-satisfying elements above it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_simpleGraph_supergraph_maximal__p2m_7fc18aad_d07a_49bb_b01c_abff1eddf2b3_a1 {α : Type} [Finite α] [Preorder α] (x : α) (Q : α → Prop) (hx : Q x) : ∃ y : α, And (Q y) (And (x ≤ y) (∀ z : α, Q z → y ≤ z → z ≤ y)) := by sorry
