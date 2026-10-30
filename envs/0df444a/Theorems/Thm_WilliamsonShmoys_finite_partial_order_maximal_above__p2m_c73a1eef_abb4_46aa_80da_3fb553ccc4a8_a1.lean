-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_partial_order_maximal_above__p2m_c73a1eef_abb4_46aa_80da_3fb553ccc4a8_a1
-- name    : WilliamsonShmoys.finite_partial_order_maximal_above__p2m_c73a1eef_abb4_46aa_80da_3fb553ccc4a8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:42:17.996822+00:00
-- url     : https://prove2.me/theorems/ef8f473e-52a5-4ccf-bcdf-3473244ef4a6
-- title:
--   Maximal element above a point in a finite partial order
-- statement:
--   In a finite partial order, every point satisfying Q lies below a Q-satisfying element that is maximal among all Q-satisfying elements above it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.finite_partial_order_maximal_above__p2m_c73a1eef_abb4_46aa_80da_3fb553ccc4a8_a1 {α : Type} [Finite α] [PartialOrder α] (Q : α → Prop) (a : α) (ha : Q a) : ∃ b : α, a ≤ b ∧ Q b ∧ (∀ c : α, b ≤ c → Q c → c = b) := by sorry
