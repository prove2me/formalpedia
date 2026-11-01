-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_predicate_maximal_bounded__p2m_465037e3_08d8_4599_8b26_f505e0dc287e_a3
-- name    : WilliamsonShmoys.finite_predicate_maximal_bounded__p2m_465037e3_08d8_4599_8b26_f505e0dc287e_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:01:08.219221+00:00
-- url     : https://prove2.me/theorems/369224c8-1773-4917-bcd2-b6344d99f478
-- title:
--   A maximal predicate witness from a bounded natural measure
-- statement:
--   This is the finite maximization step. The initial witness makes the predicate nonempty, and the bound confines its attained measure values to the finite range from 0 through N. Choose a witness attaining the largest such value; any distinct predicate witness related by R would have strictly larger measure, a contradiction. This removes the selection and maximality argument from the parent. Its independent proof route is to form the finite set of attained values in Finset.range (N + 1), take its maximum, and choose a predicate witness attaining it. The child is valid also when N is zero.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_predicate_maximal_bounded__p2m_465037e3_08d8_4599_8b26_f505e0dc287e_a3
    {α : Type}
    (R : α → α → Prop)
    (m : α → Nat)
    (N : Nat)
    (P : α → Prop)
    (hbound : ∀ a : α, P a → m a ≤ N)
    (hstrict : ∀ a b : α, R a b → a ≠ b → m a < m b)
    (a0 : α)
    (ha0 : P a0) :
    ∃ a : α, P a ∧ ∀ b : α, R a b → P b → b = a := by sorry
