-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_rank_terminal__p2m_cd1fec5c_6619_45ff_8b92_8d3bff9da8a8_a3
-- name    : WilliamsonShmoys.finite_rank_terminal__p2m_cd1fec5c_6619_45ff_8b92_8d3bff9da8a8_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:55:07.063088+00:00
-- url     : https://prove2.me/theorems/b7abd633-ec61-443f-acb6-1e6bed0ed1cc
-- title:
--   Bounded rank progress reaches a terminal state
-- statement:
--   A good state with bounded natural-valued rank can reach a good terminal state when every good nonterminal state has a good, rank-increasing successor. The path also accumulates the specified preservation relation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.finite_rank_terminal__p2m_cd1fec5c_6619_45ff_8b92_8d3bff9da8a8_a3 {α : Type} (good terminal : α → Prop) (rank : α → Nat) (bound : Nat) (step preserves : α → α → Prop) (hrefl : ∀ x, preserves x x) (htrans : ∀ {x y z}, preserves x y → preserves y z → preserves x z) (hbound : ∀ x, rank x ≤ bound) (hstep : ∀ x, good x → ¬ terminal x → ∃ y, step x y ∧ good y ∧ preserves x y ∧ rank x < rank y) (x : α) (hx : good x) : ∃ y, Relation.ReflTransGen step x y ∧ preserves x y ∧ good y ∧ terminal y := by sorry
