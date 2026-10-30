-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_of_bounded_rank__p2m_79adc0d7_3a11_418b_99ea_c41dca74eed5_a2
-- name    : WilliamsonShmoys.exists_maximal_of_bounded_rank__p2m_79adc0d7_3a11_418b_99ea_c41dca74eed5_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:01:07.714266+00:00
-- url     : https://prove2.me/theorems/cbe594ab-d087-41a8-8ae7-0fa8b55a9749
-- title:
--   Maximal element from a bounded natural rank
-- statement:
--   For candidates above a starting element, a natural rank bounded by B and strictly increasing under every proper candidate extension imply that a maximal candidate exists.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_of_bounded_rank__p2m_79adc0d7_3a11_418b_99ea_c41dca74eed5_a2 {α : Type} (le : α → α → Prop) (Q : α → Prop) (r : α → Nat) (a : α) (ha : Q a) (hrefl : le a a) (B : Nat) (hbound : ∀ x : α, le a x → Q x → r x ≤ B) (hstrict : ∀ x y : α, le a x → Q x → le x y → Q y → x ≠ y → r x < r y) : ∃ w : α, le a w ∧ Q w ∧ ∀ x : α, le w x → Q x → x = w := by sorry
