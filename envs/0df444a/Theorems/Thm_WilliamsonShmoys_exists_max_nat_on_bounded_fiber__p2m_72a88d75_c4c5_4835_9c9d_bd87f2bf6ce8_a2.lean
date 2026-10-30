-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_max_nat_on_bounded_fiber__p2m_72a88d75_c4c5_4835_9c9d_bd87f2bf6ce8_a2
-- name    : WilliamsonShmoys.exists_max_nat_on_bounded_fiber__p2m_72a88d75_c4c5_4835_9c9d_bd87f2bf6ce8_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:26:48.635061+00:00
-- url     : https://prove2.me/theorems/3e05bcc3-8f8f-4499-a67f-24ecd7b090ac
-- title:
--   Maximum of a bounded natural-valued family
-- statement:
--   Every nonempty family with a bounded natural-valued objective contains a member attaining the maximum objective value.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_max_nat_on_bounded_fiber__p2m_72a88d75_c4c5_4835_9c9d_bd87f2bf6ce8_a2
    {α : Type} (Q : α → Prop) (f : α → Nat) (N : Nat)
    (hbound : ∀ a, Q a → f a ≤ N) (hne : ∃ a, Q a) :
    ∃ a, Q a ∧ ∀ b, Q b → f b ≤ f a := by
  sorry
