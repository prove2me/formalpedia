-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_rank_maximal_extension__p2m_15a542b2_5d3b_464a_bec6_5f7385b1f62b_a1
-- name    : WilliamsonShmoys.exists_rank_maximal_extension__p2m_15a542b2_5d3b_464a_bec6_5f7385b1f62b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T17:31:44.187236+00:00
-- url     : https://prove2.me/theorems/33d33e73-0a26-4502-97a8-d2832b8beae5
-- title:
--   Rank-maximal extension in a finite preorder
-- statement:
--   In a finite preorder, if a natural-valued rank strictly increases along every proper comparable pair, every element satisfying a predicate has a predicate-satisfying extension that is maximal among comparable predicate-satisfying extensions. Choose a maximum-rank candidate among the finite eligible elements.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_rank_maximal_extension__p2m_15a542b2_5d3b_464a_bec6_5f7385b1f62b_a1
    {α : Type} [Fintype α] [Preorder α]
    (P : α → Prop) (rank : α → Nat)
    (hstrict : ∀ a b, a ≤ b → a ≠ b → rank a < rank b)
    (a : α) (ha : P a) :
    ∃ b, P b ∧ a ≤ b ∧ ∀ c, P c → b ≤ c → c ≤ b := by sorry
